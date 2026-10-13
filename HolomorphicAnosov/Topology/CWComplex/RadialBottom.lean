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

namespace HolomorphicAnosov

universe u v

/-- Hatcher's projection fixes the bottom of the characteristic prism. -/
theorem cw_prism_radial_bottom
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : Metric.closedBall (0 : E) 1) :
    cw_prism_radial (x, 0) = (x, 0) := by
  have hx : ‖x.val‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
  apply Prod.ext
  · apply Subtype.ext
    simp [cw_prism_radial, max_eq_right hx]
  · apply Subtype.ext
    simp [cw_prism_radial, max_eq_right hx]

end HolomorphicAnosov
