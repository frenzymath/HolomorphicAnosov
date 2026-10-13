import Mathlib.Topology.Connected.LocallyConnected

/-!
# Frontiers of components of open sets

Source context: Cairns (1951), Lemma 3.1 and its corollary, pp.861–862.
This is the general topological component-boundary argument used in the
bounded-component extension proof, expanded by the agent.
-/

namespace HolomorphicAnosov

open Set

/-- A component of an open set in a locally connected space has no frontier
point inside that open set. Source context: Cairns (1951), §3, pp.861–862;
the general formulation and proof are agent-written.

A connected component is closed in the open-set subtype. Therefore a point
of its ambient closure which is still in that open set belongs to the
component. Local connectedness makes the component open in the ambient space,
so such a point is interior and cannot be a frontier point. If the base point
is outside the open set, its component is empty and the conclusion is vacuous. -/
theorem frontier_connectedComponentIn_subset_compl
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    {s : Set X} (hs : IsOpen s) (x : X) :
    frontier (connectedComponentIn s x) ⊆ sᶜ := by
  by_cases hx : x ∈ s
  · intro y hy hys
    have hycl : y ∈ closure (connectedComponentIn s x) := frontier_subset_closure hy
    rw [connectedComponentIn_eq_image hx] at hycl
    have hycomp : (⟨y, hys⟩ : s) ∈ connectedComponent (⟨x, hx⟩ : s) :=
      (Topology.IsInducing.subtypeVal.isClosed_iff'.mp isClosed_connectedComponent) _ hycl
    have hyin : y ∈ connectedComponentIn s x := by
      rw [connectedComponentIn_eq_image hx]
      exact ⟨⟨y, hys⟩, hycomp, rfl⟩
    exact hy.2 (by simpa only [(hs.connectedComponentIn).interior_eq] using hyin)
  · simp [connectedComponentIn_eq_empty hx]

end HolomorphicAnosov

