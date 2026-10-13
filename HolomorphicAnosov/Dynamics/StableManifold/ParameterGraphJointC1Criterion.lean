import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphAtlasDerivative
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section
open Set
namespace HolomorphicAnosov

/-- Lowering the order retains fibre differentiability and all required joint jets. -/
theorem JointFiberContDiff.of_le
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {E : A → Type*} {F : B → Type*}
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    {e : FiniteRankNormedAtlas (E := E)} {f : FiniteRankNormedAtlas (E := F)}
    {b : A → B} {g : ∀ p, E p → F (b p)} {r s : ℕ}
    (h : JointFiberContDiff e f b r g) (hsr : s ≤ r) :
    JointFiberContDiff e f b s g := by
  refine ⟨fun p ↦ (h.1 p).of_le (by exact_mod_cast hsr), ?_⟩
  exact fun i j m hm ↦ h.2 i j m (hm.trans hsr)

/-- HPS, *Invariant Manifolds*, pp.34–35 and 61–62: a fibre derivative field
continuous in the genuine linear bundle charts makes a continuous family jointly
fibre C¹. No derivative in the parameter is taken.

The atlas derivative formula identifies L with the actual derivative of each
chart expression. Restrict its joint continuity to a fixed base point and apply
the C¹ criterion. Conjugating back by the fixed linear charts gives C¹ in the
original fibres. The zeroth jet is the value and the first jet is the derivative,
up to the canonical continuous linear currying equivalences; their prescribed
joint continuity is therefore exactly that required by JointFiberContDiff. -/
theorem parameter_graph_joint_c1_criterion
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {E : A → Type*} {F : B → Type*}
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (b : A → B) (g : ∀ p, E p → F (b p))
    (D : ∀ p, E p → E p →L[ℝ] F (b p))
    (hD : ∀ p x, HasFDerivAt (g p) (D p x) x)
    (L : ∀ i j, A × FiniteFiberModel (e.rank i) →
      FiniteFiberModel (e.rank i) →L[ℝ] FiniteFiberModel (f.rank j))
    (hL : ∀ i j p (hp : p ∈ (e.chart i).baseSet)
      (hbp : b p ∈ (f.chart j).baseSet) x,
      L i j (p, x) = (f.coordinates j (b p) hbp).toContinuousLinearMap.comp
        ((D p ((e.coordinates i p hp).symm x)).comp
          (e.coordinates i p hp).symm.toContinuousLinearMap))
    (hLc : ∀ i j, ContinuousOn (L i j)
      (((e.chart i).baseSet ∩ b ⁻¹' (f.chart j).baseSet) ×ˢ univ))
    (hgc : ∀ i j, ContinuousOn
      (fun z : A × FiniteFiberModel (e.rank i) ↦ fibreChartExpression e f b g i j z.1 z.2)
      (((e.chart i).baseSet ∩ b ⁻¹' (f.chart j).baseSet) ×ˢ univ)) :
    JointFiberContDiff e f b 1 g := by
  have hchart i j p (hp : p ∈ (e.chart i).baseSet)
      (hbp : b p ∈ (f.chart j).baseSet) x :
      HasFDerivAt (fibreChartExpression e f b g i j p) (L i j (p, x)) x := by
    rw [hL i j p hp hbp x]
    exact parameter_graph_atlas_derivative e f b g i j p hp hbp x _ (hD p _)
  constructor
  · intro p
    let cp := e.coordinates p p (e.mem_baseSet p)
    let cq := f.coordinates (b p) (b p) (f.mem_baseSet (b p))
    have hmodel : ContDiff ℝ 1 (fibreChartExpression e f b g p (b p) p) := by
      apply contDiff_one_iff_hasFDerivAt.mpr
      refine ⟨fun x ↦ L p (b p) (p, x), ?_, ?_⟩
      · exact (hLc p (b p)).comp_continuous
          (continuous_const.prodMk continuous_id)
          (fun _ ↦ ⟨⟨e.mem_baseSet p, f.mem_baseSet (b p)⟩, mem_univ _⟩)
      · exact hchart p (b p) p (e.mem_baseSet p) (f.mem_baseSet (b p))
    have heq : g p = fun x ↦ cq.symm (fibreChartExpression e f b g p (b p) p (cp x)) := by
      funext x
      have hinv : (e.chart p).toOpenPartialHomeomorph.symm (p, cp x) =
          (⟨p, x⟩ : Sigma E) := by
        have happly : (e.chart p) (⟨p, x⟩ : Sigma E) = (p, cp x) :=
          e.chart_apply p p (e.mem_baseSet p) x
        rw [← happly]
        exact (e.chart p).toOpenPartialHomeomorph.left_inv
          ((e.chart p).mem_source.mpr (e.mem_baseSet p))
      unfold fibreChartExpression
      rw [hinv]
      dsimp only
      rw [f.chart_apply (b p) (b p) (f.mem_baseSet (b p))]
      exact (cq.symm_apply_apply (g p x)).symm
    rw [heq]
    exact cq.symm.contDiff.comp (hmodel.comp cp.contDiff)
  · intro i j m hm
    have hm' : m = 0 ∨ m = 1 := by omega
    rcases hm' with rfl | rfl
    · change ContinuousOn (fun z : A × FiniteFiberModel (e.rank i) ↦
        (continuousMultilinearCurryFin0 ℝ (FiniteFiberModel (e.rank i))
          (FiniteFiberModel (f.rank j))).symm
          (fibreChartExpression e f b g i j z.1 z.2)) _
      exact (continuousMultilinearCurryFin0 ℝ (FiniteFiberModel (e.rank i))
        (FiniteFiberModel (f.rank j))).symm.continuous.comp_continuousOn (hgc i j)
    · have hcont := (continuousMultilinearCurryFin1 ℝ (FiniteFiberModel (e.rank i))
        (FiniteFiberModel (f.rank j))).symm.continuous.comp_continuousOn (hLc i j)
      apply hcont.congr
      intro z hz
      apply ContinuousMultilinearMap.ext
      intro v
      simp only [Function.comp_apply, FibreJet, iteratedFDeriv_one_apply,
        continuousMultilinearCurryFin1_symm_apply]
      rw [(hchart i j z.1 hz.1.1 hz.1.2 z.2).fderiv]

end HolomorphicAnosov
