import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Separation.Hausdorff

open Set Filter
open scoped Topology _root_.Topology

namespace HolomorphicAnosov.Topology

/-- Source: Tao, 246C Notes 2 (2018), Theorem 20 proof, inverse-map boundary exclusion,
`literature/Tao-246C-Notes2-2018.txt:267`. If points of a subset approach an ambient point
outside that subset and their images under a homeomorphism approach a limit in the ambient
target, that limit lies in the frontier of the open target subset. It belongs to the target
closure because every image point lies in the target. If it belonged to the target itself,
continuity of the inverse would give a second ambient limit inside the source subset,
contradicting Hausdorff uniqueness. The filter must be nontrivial. This general filter
formulation is an agent-written expansion of the source's inverse-map argument. -/
theorem Homeomorph.limit_mem_frontier
    {X Y ι : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    {S : Set X} {T : Set Y} (e : S ≃ₜ T) (hT : IsOpen T) {L : Filter ι} [NeBot L]
    (x : ι → S) {p : X} {q : Y}
    (hx : Tendsto (fun i ↦ (x i : X)) L (𝓝 p)) (hp : p ∉ S)
    (hy : Tendsto (fun i ↦ (e (x i) : Y)) L (𝓝 q)) : q ∈ frontier T := by
  rw [hT.frontier_eq]
  refine ⟨mem_closure_of_tendsto hy (Eventually.of_forall fun i ↦ (e (x i)).property), ?_⟩
  intro hq
  have hyT : Tendsto (fun i ↦ e (x i)) L (𝓝 (⟨q, hq⟩ : T)) :=
    tendsto_subtype_rng.mpr hy
  have hinv : Tendsto (fun i ↦ x i) L (𝓝 (e.symm ⟨q, hq⟩)) := by
    simpa only [Function.comp_def, e.symm_apply_apply] using
      e.continuous_symm.continuousAt.tendsto.comp hyT
  have heq : p = (e.symm ⟨q, hq⟩ : X) :=
    tendsto_nhds_unique hx (tendsto_subtype_rng.mp hinv)
  exact hp (heq ▸ (e.symm ⟨q, hq⟩).property)


end HolomorphicAnosov.Topology
