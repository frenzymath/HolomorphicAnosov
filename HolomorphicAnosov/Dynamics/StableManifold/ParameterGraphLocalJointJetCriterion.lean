import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointJetCriterion
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalFiberRegularity

noncomputable section
open Set _root_.Topology
open scoped ContDiff
namespace HolomorphicAnosov

/-- HPS pp.32–36,62: original local jet evaluation continuity packages into
local joint fibre regularity. Restrict the source frame anchors to the given
original domain U. On each source/receiving overlap, the target chart turns
continuous original jet evaluations into continuous coordinate evaluations.
Finite-dimensional multilinear extensionality gives chart-jet continuity.
The linear chart identity is valid without global smoothness, so only the
actual C^r germs on U are needed; no conclusion outside U is assumed. -/
theorem parameter_graph_local_joint_jet_criterion
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {E : A → Type*} {F : B → Type*}
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (b : A → B) (g : ∀ p, E p → F (b p)) (r : ℕ) (U : Set (Sigma E))
    (hg : ∀ z ∈ U, ContDiffAt ℝ (r : ℕ∞ω) (g z.1) z.2)
    (hJ : ∀ i m, m ≤ r → ContinuousOn
      (fun z : (e.chart i).baseSet ×
          (FiniteFiberModel (e.rank i) × (Fin m → FiniteFiberModel (e.rank i))) ↦
        (⟨b z.1.val, iteratedFDeriv ℝ m (g z.1.val)
          ((e.coordinates i z.1.val z.1.property).symm z.2.1)
          (fun a ↦ (e.coordinates i z.1.val z.1.property).symm (z.2.2 a))⟩ : Sigma F))
      {z | (⟨z.1.val,(e.coordinates i z.1.val z.1.property).symm z.2.1⟩ : Sigma E) ∈ U}) :
    JointFiberContDiffOn e f b r U g := by
  refine ⟨hg,?_⟩
  intro i j m hm
  rw [continuousOn_iff_continuous_domRestrict]
  apply parameter_graph_multilinear_continuous_of_eval
  intro v
  let S : Set (A × FiniteFiberModel (e.rank i)) :=
    {z | z.1 ∈ (e.chart i).baseSet ∩ b ⁻¹' (f.chart j).baseSet ∧
      (e.chart i).toOpenPartialHomeomorph.symm z ∈ U}
  let H : S → (e.chart i).baseSet ×
      (FiniteFiberModel (e.rank i) × (Fin m → FiniteFiberModel (e.rank i))) :=
    fun z ↦ (⟨z.val.1,z.property.1.1⟩,(z.val.2,v))
  have hH : Continuous H :=
    (continuous_subtype_val.fst.subtype_mk _).prodMk
      (continuous_subtype_val.snd.prodMk continuous_const)
  have hHU (z : S) : (⟨z.1.1,(e.coordinates i z.1.1 z.2.1.1).symm z.1.2⟩ : Sigma E) ∈ U := by
    have heq : (e.chart i).toOpenPartialHomeomorph.symm z.1 =
        (⟨z.1.1,(e.coordinates i z.1.1 z.2.1.1).symm z.1.2⟩ : Sigma E) := by
      have hc : e.chart i
          (⟨z.1.1,(e.coordinates i z.1.1 z.2.1.1).symm z.1.2⟩ : Sigma E) = z.1 := by
        rw [e.chart_apply i z.1.1 z.2.1.1]
        simp
      exact (congrArg (e.chart i).toOpenPartialHomeomorph.symm hc).symm.trans
        ((e.chart i).toOpenPartialHomeomorph.left_inv ((e.chart i).mem_source.mpr z.2.1.1))
    exact heq ▸ z.2.2
  have heval := (hJ i m hm).comp_continuous hH hHU
  have hchart := (f.chart j).toOpenPartialHomeomorph.continuousOn.comp_continuous heval
    (fun z : S ↦ (f.chart j).mem_source.mpr z.property.1.2)
  apply hchart.snd.congr
  intro z
  change _ = FibreJet m (fibreChartExpression e f b g i j z.val.1) z.val.2 v
  rw [parameter_graph_atlas_iterated_derivative_of_equiv e f b g i j z.val.1
    z.property.1.1 z.property.1.2 m z.val.2 v]
  exact congrArg Prod.snd (f.chart_apply j (b z.val.1) z.property.1.2 _)

end HolomorphicAnosov
