import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
open Set Topology
namespace HolomorphicAnosov

/-- Continuity of a finite dimensional multilinear operator family follows from
continuity at every fixed vector tuple. Curry off the first input and use the
finite dimensional continuous-linear-map evaluation criterion inductively;
arity zero is the canonical equivalence with the receiving space. This is the
finite-model operator-topology step used for HPS p.62 fibre jet continuity. -/
theorem parameter_graph_multilinear_continuous_of_eval
    {Z V W : Type*} [TopologicalSpace Z]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (m : ℕ) (L : Z → ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ V) W)
    (hL : ∀v,Continuous (fun z ↦ L z v)) : Continuous L := by
  induction m with
  | zero =>
      rw [← (continuousMultilinearCurryFin0 ℝ V W).comp_continuous_iff]
      exact hL 0
  | succ m ih =>
      rw [← (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1) ↦ V) W).comp_continuous_iff,
        continuous_clm_apply]
      intro v
      apply ih
      intro w
      exact hL (Fin.cons v w)

/-- Higher derivatives in linear bundle charts are conjugated original fibre
derivatives. Identify the chart expression with the receiving linear chart
composed with the original map and the inverse source chart. The iterated
derivative chain rules for these linear maps give the formula at every order,
including order zero. Both chart maps are equivalences, so this exact identity
holds even without a smoothness hypothesis. HPS pp.8 and 62. -/
theorem parameter_graph_atlas_iterated_derivative_of_equiv
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {E : A → Type*} {F : B → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (b : A → B) (g : ∀p,E p → F (b p))
    (i : A) (j : B) (p : A) (hp : p ∈ (e.chart i).baseSet)
    (hbp : b p ∈ (f.chart j).baseSet) (m : ℕ)
    (x : FiniteFiberModel (e.rank i)) (v : Fin m → FiniteFiberModel (e.rank i)) :
    FibreJet m (fibreChartExpression e f b g i j p) x v =
      f.coordinates j (b p) hbp
        (iteratedFDeriv ℝ m (g p) ((e.coordinates i p hp).symm x)
          (fun a ↦ (e.coordinates i p hp).symm (v a))) := by
  have heq : fibreChartExpression e f b g i j p =
      (f.coordinates j (b p) hbp) ∘ (g p) ∘ (e.coordinates i p hp).symm := by
    funext y
    have happly : (e.chart i)
        (⟨p,(e.coordinates i p hp).symm y⟩ : Sigma E) = (p,y) := by
      rw [e.chart_apply i p hp]
      simp
    have hinv : (e.chart i).toOpenPartialHomeomorph.symm (p,y) =
        (⟨p,(e.coordinates i p hp).symm y⟩ : Sigma E) := by
      rw [← happly]
      exact (e.chart i).toOpenPartialHomeomorph.left_inv ((e.chart i).mem_source.mpr hp)
    unfold fibreChartExpression
    rw [hinv]
    exact congrArg Prod.snd (f.chart_apply j (b p) hbp _)
  rw [heq]
  unfold FibreJet
  rw [(f.coordinates j (b p) hbp).iteratedFDeriv_comp_left]
  have hi := (e.coordinates i p hp).symm.iteratedFDerivWithin_comp_right
    (g p) uniqueDiffOn_univ (x := x) (mem_univ _) m
  simp only [preimage_univ, iteratedFDerivWithin_univ] at hi
  rw [hi]
  rfl

set_option linter.unusedVariables false in
/-- Compatibility form of exact chart transport for a C^r input family. -/
theorem parameter_graph_atlas_iterated_derivative
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {E : A → Type*} {F : B → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (b : A → B) (g : ∀p,E p → F (b p)) (r : ℕ)
    (hg : ∀p,ContDiff ℝ r (g p))
    (i : A) (j : B) (p : A) (hp : p ∈ (e.chart i).baseSet)
    (hbp : b p ∈ (f.chart j).baseSet) (m : ℕ) (hm : m ≤ r)
    (x : FiniteFiberModel (e.rank i)) (v : Fin m → FiniteFiberModel (e.rank i)) :
    FibreJet m (fibreChartExpression e f b g i j p) x v =
      f.coordinates j (b p) hbp
        (iteratedFDeriv ℝ m (g p) ((e.coordinates i p hp).symm x)
          (fun a ↦ (e.coordinates i p hp).symm (v a))) := by
  exact parameter_graph_atlas_iterated_derivative_of_equiv e f b g i j p hp hbp m x v

/-- HPS pp.35 and 62: continuous original jet evaluations through order r
give joint fibre C^r regularity. On each source chart and receiving overlap,
apply the target chart to the original jet evaluated at its inverse source
frame. The preceding conjugation formula identifies this with the chart jet
evaluation. Finite dimensional multilinear evaluation continuity upgrades
these scalar evaluations to operator continuity, at every order including zero.
The supplied fibre regularity gives the other clause of JointFiberContDiff. -/
theorem parameter_graph_joint_jet_criterion
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {E : A → Type*} {F : B → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (b : A → B) (g : ∀p,E p → F (b p)) (r : ℕ)
    (hg : ∀p,ContDiff ℝ r (g p))
    (hJ : ∀i m,m ≤ r → Continuous
      (fun z : (e.chart i).baseSet ×
          (FiniteFiberModel (e.rank i) × (Fin m → FiniteFiberModel (e.rank i))) ↦
        (⟨b z.1.val,iteratedFDeriv ℝ m (g z.1.val)
          ((e.coordinates i z.1.val z.1.property).symm z.2.1)
          (fun a ↦ (e.coordinates i z.1.val z.1.property).symm (z.2.2 a))⟩ : Sigma F))) :
    JointFiberContDiff e f b r g := by
  refine ⟨hg,?_⟩
  intro i j m hm
  rw [continuousOn_iff_continuous_domRestrict]
  apply parameter_graph_multilinear_continuous_of_eval
  intro v
  let S := (((e.chart i).baseSet ∩ b ⁻¹' (f.chart j).baseSet) ×ˢ
    (univ : Set (FiniteFiberModel (e.rank i))))
  let H : S → (e.chart i).baseSet ×
      (FiniteFiberModel (e.rank i) × (Fin m → FiniteFiberModel (e.rank i))) :=
    fun z ↦ (⟨z.val.1,z.property.1.1⟩,(z.val.2,v))
  have hH : Continuous H :=
    (continuous_subtype_val.fst.subtype_mk _).prodMk
      (continuous_subtype_val.snd.prodMk continuous_const)
  have heval := (hJ i m hm).comp hH
  have hchart := (f.chart j).toOpenPartialHomeomorph.continuousOn.comp_continuous heval
    (fun z : S ↦ (f.chart j).mem_source.mpr z.property.1.2)
  apply hchart.snd.congr
  intro z
  change _ = FibreJet m (fibreChartExpression e f b g i j z.val.1) z.val.2 v
  rw [parameter_graph_atlas_iterated_derivative e f b g r hg i j z.val.1
    z.property.1.1 z.property.1.2 m hm z.val.2 v]
  exact congrArg Prod.snd (f.chart_apply j (b z.val.1) z.property.1.2 _)

end HolomorphicAnosov
