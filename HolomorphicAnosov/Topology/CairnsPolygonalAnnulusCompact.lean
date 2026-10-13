import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.PathConnected

/-!
# Compactness of the closed Cairns annulus

This provider isolates the compact intersection used by the prescribed-boundary
parameterization: `R \ interior D` is compact when R is compact.
-/

open Set
namespace HolomorphicAnosov.Topology

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- The closed region `R \ interior D` is compact whenever R is compact. -/
theorem cairns_polygonal_annulus_compact
    (D R : Set Plane) (hcompactR : IsCompact R) :
    IsCompact (R \ interior D) := by
  exact hcompactR.inter_right isOpen_interior.isClosed_compl

end HolomorphicAnosov.Topology

