import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphAtlasDerivative
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section
open Set Topology Filter
namespace HolomorphicAnosov

/-- HPS pp.35 and 61–62: joint fibre regularity gives continuous evaluation of
its actual first derivative along continuous point and tangent-vector families.
Work locally in genuine source and target charts. The first chart jet is
jointly continuous, and its evaluation on the continuous coordinate vector is
continuous. The chain rule identifies that value with the target coordinates
of the original derivative. The inverse target chart proves the claim in the
supplied total-space topology; the parameter space itself need not be smooth. -/
theorem parameter_graph_joint_derivative_evaluation
    {A B Z : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace Z]
    {E : A → Type*} {F : B → Type*}
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (b : A → B) (hb : Continuous b) (g : ∀ p, E p → F (b p))
    (r : ℕ) (hr : 1 ≤ r) (hg : JointFiberContDiff e f b r g)
    (p : Z → A) (hp : Continuous p) (x v : ∀ z, E (p z))
    (hx : Continuous (fun z ↦ (⟨p z,x z⟩ : Sigma E)))
    (hv : Continuous (fun z ↦ (⟨p z,v z⟩ : Sigma E))) :
    Continuous (fun z ↦ (⟨b (p z), fderiv ℝ (g (p z)) (x z) (v z)⟩ : Sigma F)) := by
  apply continuous_iff_continuousAt.mpr
  intro z₀
  let i := p z₀
  let j := b (p z₀)
  let xc : Z → FiniteFiberModel (e.rank i) := fun z ↦ (e.chart i ⟨p z,x z⟩).2
  let vc : Z → FiniteFiberModel (e.rank i) := fun z ↦ (e.chart i ⟨p z,v z⟩).2
  have hxc : ContinuousAt xc z₀ :=
    ((e.chart i).continuousAt (by exact (e.chart i).mem_source.mpr (e.mem_baseSet i))).snd.comp hx.continuousAt
  have hvc : ContinuousAt vc z₀ :=
    ((e.chart i).continuousAt (by exact (e.chart i).mem_source.mpr (e.mem_baseSet i))).snd.comp hv.continuousAt
  have hopen : IsOpen (((e.chart i).baseSet ∩ b ⁻¹' (f.chart j).baseSet) ×ˢ
      (univ : Set (FiniteFiberModel (e.rank i)))) :=
    ((e.chart i).open_baseSet.inter ((f.chart j).open_baseSet.preimage hb)).prod isOpen_univ
  have hmem : (p z₀,xc z₀) ∈ (((e.chart i).baseSet ∩ b ⁻¹' (f.chart j).baseSet) ×ˢ
      (univ : Set (FiniteFiberModel (e.rank i)))) :=
    ⟨⟨e.mem_baseSet i,f.mem_baseSet j⟩,mem_univ _⟩
  have hj := ((hg.2 i j 1 hr).continuousAt (hopen.mem_nhds hmem)).comp
    (f := fun z ↦ (p z,xc z)) (hp.continuousAt.prodMk hxc)
  let L : Z → FiniteFiberModel (e.rank i) →L[ℝ] FiniteFiberModel (f.rank j) :=
    fun z ↦ (continuousMultilinearCurryFin1 ℝ (FiniteFiberModel (e.rank i))
      (FiniteFiberModel (f.rank j)))
      (FibreJet 1 (fibreChartExpression e f b g i j (p z)) (xc z))
  have hL : ContinuousAt L z₀ :=
    (continuousMultilinearCurryFin1 ℝ _ _).continuous.continuousAt.comp hj
  have heval : ContinuousAt (fun z ↦ L z (vc z)) z₀ := hL.clm_apply hvc
  apply (f.chart j).continuousAt_of_comp_left
    (show ContinuousAt (fun z : Z ↦ (⟨b (p z), fderiv ℝ (g (p z)) (x z) (v z)⟩ : Sigma F).1) z₀ from
      (hb.comp hp).continuousAt) (f.mem_baseSet j)
  apply ((hb.comp hp).continuousAt.prodMk heval).congr_of_eventuallyEq
  have hne : ∀ᶠ z in 𝓝 z₀, p z ∈ (e.chart i).baseSet :=
    hp.continuousAt.eventually ((e.chart i).open_baseSet.mem_nhds (e.mem_baseSet i))
  have hnf : ∀ᶠ z in 𝓝 z₀, b (p z) ∈ (f.chart j).baseSet :=
    (hb.comp hp).continuousAt.eventually ((f.chart j).open_baseSet.mem_nhds (f.mem_baseSet j))
  filter_upwards [hne,hnf] with z he hf
  dsimp only [Function.comp_apply]
  rw [f.chart_apply j (b (p z)) hf]
  congr 1
  have hD := parameter_graph_atlas_derivative e f b g i j (p z) he hf (xc z)
    (fderiv ℝ (g (p z)) (x z))
    (by
      have hcoord : (e.coordinates i (p z) he).symm (xc z) = x z := by
        dsimp [xc]
        rw [e.chart_apply i (p z) he]
        simp
      rw [hcoord]
      exact ((hg.1 (p z)).differentiable (by exact_mod_cast (show r ≠ 0 by omega)) (x z)).hasFDerivAt)
  have hcoordv : vc z = e.coordinates i (p z) he (v z) := by
    dsimp [vc]; rw [e.chart_apply i (p z) he]
  dsimp [L]
  simp only [FibreJet, iteratedFDeriv_one_apply]
  rw [hD.fderiv, hcoordv]
  simp

/-- Zeroth chart jets recover continuity of the actual total fibre map. -/
theorem parameter_graph_joint_value_continuous
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {E : A → Type*} {F : B → Type*}
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (b : A → B) (hb : Continuous b) (g : ∀ p, E p → F (b p))
    (r : ℕ) (hg : JointFiberContDiff e f b r g) :
    Continuous (fun z : Sigma E ↦ (⟨b z.1,g z.1 z.2⟩ : Sigma F)) := by
  apply continuous_iff_continuousAt.mpr
  intro z₀
  let i := z₀.1
  let j := b z₀.1
  have hproj : ContinuousAt (fun z : Sigma E ↦ z.1) z₀ :=
    (e.chart i).continuousAt_proj ((e.chart i).mem_source.mpr (e.mem_baseSet i))
  have hchart : ContinuousAt (e.chart i) z₀ :=
    (e.chart i).continuousAt ((e.chart i).mem_source.mpr (e.mem_baseSet i))
  have hbase : (e.chart i z₀).1 = z₀.1 := (e.chart i).proj_toFun _
    ((e.chart i).mem_source.mpr (e.mem_baseSet i))
  have hopen : IsOpen (((e.chart i).baseSet ∩ b ⁻¹' (f.chart j).baseSet) ×ˢ
      (univ : Set (FiniteFiberModel (e.rank i)))) :=
    ((e.chart i).open_baseSet.inter ((f.chart j).open_baseSet.preimage hb)).prod isOpen_univ
  have hmem : e.chart i z₀ ∈ (((e.chart i).baseSet ∩ b ⁻¹' (f.chart j).baseSet) ×ˢ
      (univ : Set (FiniteFiberModel (e.rank i)))) := by
    exact ⟨⟨hbase ▸ e.mem_baseSet i,hbase ▸ f.mem_baseSet j⟩,mem_univ _⟩
  have hj := ((hg.2 i j 0 (Nat.zero_le r)).continuousAt (hopen.mem_nhds hmem)).comp hchart
  have hval : ContinuousAt (fun z : Sigma E ↦
      fibreChartExpression e f b g i j (e.chart i z).1 (e.chart i z).2) z₀ := by
    have hc := (continuousMultilinearCurryFin0 ℝ (FiniteFiberModel (e.rank i))
      (FiniteFiberModel (f.rank j))).continuous.continuousAt.comp hj
    simpa only [FibreJet, iteratedFDeriv_zero_eq_comp, Function.comp_def,
      LinearIsometryEquiv.apply_symm_apply] using hc
  apply (f.chart j).continuousAt_of_comp_left
    (show ContinuousAt (fun z : Sigma E ↦ (⟨b z.1,g z.1 z.2⟩ : Sigma F).1) z₀ from
      hb.continuousAt.comp hproj) (f.mem_baseSet j)
  apply ((hb.continuousAt.comp hproj).prodMk hval).congr_of_eventuallyEq
  have he : ∀ᶠ z : Sigma E in 𝓝 z₀, z.1 ∈ (e.chart i).baseSet :=
    hproj.eventually ((e.chart i).open_baseSet.mem_nhds (e.mem_baseSet i))
  have hf : ∀ᶠ z : Sigma E in 𝓝 z₀, b z.1 ∈ (f.chart j).baseSet :=
    (hb.continuousAt.comp hproj).eventually
      ((f.chart j).open_baseSet.mem_nhds (f.mem_baseSet j))
  filter_upwards [he,hf] with z he hf
  dsimp only [Function.comp_apply, fibreChartExpression]
  change f.chart j ⟨b z.1,g z.1 z.2⟩ = (b z.1,
    (f.chart j ⟨b ((e.chart i).toOpenPartialHomeomorph.symm (e.chart i z)).1,
      g ((e.chart i).toOpenPartialHomeomorph.symm (e.chart i z)).1
        ((e.chart i).toOpenPartialHomeomorph.symm (e.chart i z)).2⟩).2)
  have hinv : (e.chart i).toOpenPartialHomeomorph.symm (e.chart i z) = z :=
    (e.chart i).toOpenPartialHomeomorph.left_inv ((e.chart i).mem_source.mpr he)
  rw [hinv]
  rw [f.chart_apply j (b z.1) hf]

end HolomorphicAnosov
