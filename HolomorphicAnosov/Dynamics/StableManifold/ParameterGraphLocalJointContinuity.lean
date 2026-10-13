import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalFiberRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalJointJetNorm
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalJointJetCriterion
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphAtlasOperations

noncomputable section
open Set _root_.Topology
open scoped ContDiff
namespace HolomorphicAnosov

variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
  {E : A → Type*} {F : B → Type*}
  [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
  [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]
  [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]

/-- HPS pp.32–36,62: the zeroth local jet is the value itself, so local joint
regularity on an open original domain implies continuity of the total map.
Apply original jet evaluation to the tautological anchor on the domain subtype. -/
theorem parameter_graph_local_joint_value_continuous
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (b : A → B) (hb : Continuous b) (g : ∀ p, E p → F (b p))
    (r : ℕ) (U : Set (Sigma E)) (hU : IsOpen U)
    (hg : JointFiberContDiffOn e f b r U g) :
    ContinuousOn (fun z : Sigma E ↦ (⟨b z.1,g z.1 z.2⟩ : Sigma F)) U := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun z : U ↦ (⟨b z.1.1,g z.1.1 z.1.2⟩ : Sigma F))
  have h := parameter_graph_local_jet_evaluation_continuous e f b hb g r 0 (Nat.zero_le r)
    U hU hg (fun z : U ↦ z.1.1)
    ((parameter_graph_atlas_projection_continuous e).comp continuous_subtype_val)
    (fun z ↦ z.1.2) continuous_subtype_val (fun z ↦ z.2)
    (fun _ ↦ (0 : Fin 0 → _)) (fun i ↦ Fin.elim0 i)
  simpa only [iteratedFDeriv_zero_apply,Set.domRestrict] using h

/-- On an original open domain, local joint order zero is exactly continuity
of the total value map. For the reverse implication, each original fibre
inclusion is inducing, so total continuity gives fibre continuity on the open
fibre slice, hence the required order-zero germ. Inverse source frames pull
back total continuity to the zeroth jet evaluation needed by the local criterion. -/
theorem parameter_graph_local_joint_zero_iff
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (b : A → B) (hb : Continuous b) (g : ∀ p, E p → F (b p))
    (U : Set (Sigma E)) (hU : IsOpen U) :
    JointFiberContDiffOn e f b 0 U g ↔
      ContinuousOn (fun z : Sigma E ↦ (⟨b z.1,g z.1 z.2⟩ : Sigma F)) U := by
  refine ⟨parameter_graph_local_joint_value_continuous e f b hb g 0 U hU,?_⟩
  intro hg
  apply parameter_graph_local_joint_jet_criterion
  · intro z hz
    let S : Set (E z.1) := {x | (⟨z.1,x⟩ : Sigma E) ∈ U}
    have hS : IsOpen S := hU.preimage (e.fibre_inducing z.1).continuous
    have hgs : ContinuousOn (g z.1) S := by
      apply (f.fibre_inducing (b z.1)).continuousOn_iff.mpr
      exact hg.comp (e.fibre_inducing z.1).continuous.continuousOn (fun _ hx ↦ hx)
    exact contDiffAt_zero.mpr ⟨S,hS.mem_nhds hz,hgs⟩
  · intro i m hm
    have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
    subst m
    simp only [iteratedFDeriv_zero_apply]
    have hc : Continuous (fun z : (e.chart i).baseSet ×
        (FiniteFiberModel (e.rank i) × (Fin 0 → FiniteFiberModel (e.rank i))) ↦
        (⟨z.1.val,(e.coordinates i z.1.val z.1.property).symm z.2.1⟩ : Sigma E)) :=
      (atlas_frame_continuous e i).comp (continuous_fst.prodMk continuous_snd.fst)
    exact hg.comp hc.continuousOn (fun _ hz ↦ hz)

/-- HPS pp.8,32–36,62: known original local jets admit a uniform norm bound
on every compact subset of the regularity domain. Restrict continuous original
jet norm to the compact subset and bound its real image; increase the bound to
its maximum with zero. Neither compactness of the whole base nor a disc shape
for the subset is required. -/
theorem parameter_graph_local_jet_norm_bounded_on_compact
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (b : A → B) (hb : Continuous b) (g : ∀ p, E p → F (b p))
    (r m : ℕ) (hm : m ≤ r) (U : Set (Sigma E)) (hU : IsOpen U)
    (hg : JointFiberContDiffOn e f b r U g) (K : Set (Sigma E))
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ‖iteratedFDeriv ℝ m (g z.1) z.2‖ ≤ C := by
  have hn := (parameter_graph_local_jet_norm_continuousOn e f b hb g r m hm U hU hg).mono hKU
  obtain ⟨C,hC⟩ := hK.bddAbove_image hn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro z hz
  exact (hC ⟨z,hz,rfl⟩).trans (le_max_left _ _)

end HolomorphicAnosov
