import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.PathConnected

/-!
# Frontier inclusion for the literal polygonal annulus

This elementary provider isolates the subtype-membership step used by the
Cairns exterior-annulus construction.  The source argument is the compact
frontier theorem together with `D ⊆ interior R`: a frontier point of `D` lies
in `D`, hence in `R`, while it cannot lie in `interior D`.
-/

open Set
namespace HolomorphicAnosov.Topology

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- The polygon frontier lies in the closed region between `D` and `R`. -/
theorem cairns_polygonal_annulus_frontier_subset
    (D R : Set Plane) (hcompact : IsCompact D)
    (hcontain : D ⊆ interior R) :
    frontier D ⊆ R \ interior D := by
  intro x hx
  refine ⟨interior_subset (hcontain (hcompact.isClosed.frontier_subset hx)), hx.2⟩

end HolomorphicAnosov.Topology

