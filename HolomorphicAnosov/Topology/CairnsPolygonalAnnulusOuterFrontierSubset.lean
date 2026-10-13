import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Outer frontier inclusion for the literal polygonal annulus

This provider isolates the elementary subtype-membership step used by the
prescribed-boundary parameterization.  A compact rectangle contains D in its
interior, so each point of frontier R lies in R and cannot lie in interior D.
-/

open Set
namespace HolomorphicAnosov.Topology

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- The rectangle frontier lies in the closed region outside `interior D`. -/
theorem cairns_polygonal_annulus_outer_frontier_subset
    (D R : Set Plane) (hRcompact : IsCompact R)
    (hcontain : D ⊆ interior R) :
    frontier R ⊆ R \ interior D := by
  intro x hx
  refine ⟨hRcompact.isClosed.frontier_subset hx, ?_⟩
  intro hd
  exact hx.2 (hcontain (interior_subset hd))

end HolomorphicAnosov.Topology

