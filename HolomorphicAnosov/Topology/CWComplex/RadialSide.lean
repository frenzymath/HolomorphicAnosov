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

namespace HolomorphicAnosov

universe u v

/-- Hatcher's projection fixes the side of the characteristic prism. -/
theorem cw_prism_radial_side
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : Metric.closedBall (0 : E) 1) (u : unitInterval) (hx : ‖x.val‖ = 1) :
    cw_prism_radial (x, u) = (x, u) := by
  have hu : (2 - (u : ℝ)) / 2 ≤ 1 := by
    have := u.property.1
    linarith
  apply Prod.ext
  · apply Subtype.ext
    simp [cw_prism_radial, hx, max_eq_left hu]
  · apply Subtype.ext
    simp [cw_prism_radial, hx, max_eq_left hu]

end HolomorphicAnosov
