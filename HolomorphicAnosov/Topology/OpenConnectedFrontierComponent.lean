import Mathlib.Topology.Connected.Basic

/-!
# An open connected set as a frontier complement component

This file proves the elementary component statement for an open preconnected set. (Whyburn, III(2.3))
-/

open Set

namespace HolomorphicAnosov

/-- An open preconnected set containing `x` is the connected component of the complement of its frontier that contains `x`. (Whyburn, III(2.3)) -/
theorem open_connected_frontier_component {X : Type*} [TopologicalSpace X]
    {D : Set X} (hD : IsOpen D) (hc : IsPreconnected D) {x : X} (hx : x ∈ D) :
    connectedComponentIn (frontier D)ᶜ x = D := by
  have havoid : D ⊆ (frontier D)ᶜ := by
    intro y hy hfront
    exact (hD.frontier_eq ▸ hfront).2 hy
  apply Set.Subset.antisymm
  · apply isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hD
      ⟨x, mem_connectedComponentIn (havoid hx), hx⟩
    rintro y ⟨hyClosure, hyComponent⟩
    by_contra hy
    exact connectedComponentIn_subset (frontier D)ᶜ x hyComponent
      (hD.frontier_eq.symm ▸ ⟨hyClosure, hy⟩)
  · exact hc.subset_connectedComponentIn hx havoid

end HolomorphicAnosov

