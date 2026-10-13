import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Disjoint frontiers for the nested Cairns annulus

This elementary provider isolates the fact that a compact set contained in the
interior of a compact rectangle has disjoint frontiers.  It is used when the
annulus boundary is decomposed into its inner and outer components.
-/

open Set
namespace HolomorphicAnosov.Topology

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- Frontiers of D and R are disjoint when D lies in interior R. -/
theorem cairns_polygonal_annulus_frontier_disjoint
    (D R : Set Plane) (hcompactD : IsCompact D)
    (hcontain : D ⊆ interior R) :
    Disjoint (frontier D) (frontier R) := by
  apply Set.disjoint_left.mpr
  intro x hD hR
  exact hR.2 (hcontain (hcompactD.isClosed.frontier_subset hD))

end HolomorphicAnosov.Topology

