import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Connected.LocallyPathConnected

/-! A covering space of a locally path connected space is locally path connected. (Hatcher,
pp.56–57) -/

open Set Filter
open scoped Topology _root_.Topology

namespace HolomorphicAnosov.Ghys

/-- A covering of a locally path connected space is locally path connected. (Hatcher, pp.56–57) -/
theorem projective_cover_cover_locallyPathConnected_gap
    {M : Type u} {E : Type v} [TopologicalSpace M] [TopologicalSpace E]
    [LocallyPathConnectedSpace M]
    (p : E → M) (hp : IsCoveringMap p) : LocallyPathConnectedSpace E := by
  refine ⟨fun x ↦ ⟨fun s ↦ ⟨fun hs ↦ ?_, fun ⟨u, hu⟩ ↦ Filter.mem_of_superset hu.1.1 hu.2⟩⟩⟩
  obtain ⟨e, hx, _⟩ := hp.isLocalHomeomorph x
  let t := s ∩ e.source
  have ht : t ∈ 𝓝 x := inter_mem hs (e.open_source.mem_nhds hx)
  refine ⟨e.symm '' pathComponentIn (e '' t) (e x), ⟨?_, ?_⟩, (?_ : _ ⊆ t).trans inter_subset_left⟩
  · nth_rewrite 1 [← e.left_inv hx]
    apply e.symm.image_mem_nhds (e.map_source hx)
    exact pathComponentIn_mem_nhds <| e.image_mem_nhds hx ht
  · refine (isPathConnected_pathComponentIn <| mem_image_of_mem e (mem_of_mem_nhds ht)).image' ?_
    refine e.continuousOn_symm.mono ?_
    unfold t
    grw [pathComponentIn_subset, inter_subset_right, e.image_source_subset]
  · exact (image_mono pathComponentIn_subset).trans
      (PartialEquiv.symm_image_image_of_subset_source _ inter_subset_right).subset


end HolomorphicAnosov.Ghys
