import HolomorphicAnosov.Topology.EuclideanDiskUnitCube
import HolomorphicAnosov.Topology.CWComplex.CharacteristicContinuity
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Homotopy.Basic
import HolomorphicAnosov.Topology.CWComplex.PairExtensionOfRetraction
import HolomorphicAnosov.Topology.CWComplex.RadialScaleBounds
import HolomorphicAnosov.Topology.CWComplex.RadialHeightBounds
import HolomorphicAnosov.Topology.CWComplex.RadialNormBound
import HolomorphicAnosov.Topology.CWComplex.RadialProjection
import HolomorphicAnosov.Topology.CWComplex.ContinuousRadialProjection
import HolomorphicAnosov.Topology.CWComplex.RadialBottom
import HolomorphicAnosov.Topology.CWComplex.RadialSide
import HolomorphicAnosov.Topology.CWComplex.RadialBoundaryTarget

namespace HolomorphicAnosov

universe u v

/-- On a characteristic boundary, the radial formula gives the original point in
the lower skeleton. This is the compatibility needed at cell attachments. -/
theorem cw_prism_radial_characteristic_frontier
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (n : ℕ) (i : Topology.RelCWComplex.cell (Set.univ : Set X) n)
    (z : Metric.closedBall (0 : Fin n → ℝ) 1) (t : unitInterval)
    (hz : ‖z.val‖ = 1) :
    (Topology.RelCWComplex.map n i (cw_prism_radial (z, t)).1.val,
      (cw_prism_radial (z, t)).2) =
      (Topology.RelCWComplex.map n i z.val, t) ∧
    Topology.RelCWComplex.map n i z.val ∈
      (Topology.CWComplex.skeletonLT (Set.univ : Set X) (n : ℕ∞) : Set X) := by
  constructor
  · rw [cw_prism_radial_side z t hz]
  · apply Topology.CWComplex.cellFrontier_subset_skeletonLT n i
    change Topology.RelCWComplex.map n i z.val ∈
      Topology.RelCWComplex.map n i '' Metric.sphere (0 : Fin n → ℝ) 1
    exact ⟨z.val, by simpa only [Metric.mem_sphere, dist_zero_right] using hz, rfl⟩

end HolomorphicAnosov
