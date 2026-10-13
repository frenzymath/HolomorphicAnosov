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
import HolomorphicAnosov.Topology.CWComplex.RadialCharacteristicFrontier
import HolomorphicAnosov.Topology.CWComplex.RadialCharacteristicTarget
import HolomorphicAnosov.Topology.CWComplex.CompatibleSkeleta
import HolomorphicAnosov.Topology.CWComplex.SubtypeGlueCharacteristicDoublePrisms
import HolomorphicAnosov.Topology.CWComplex.CellBoundaryNeSameDimInterior
import HolomorphicAnosov.Topology.CWComplex.RadialSameDimCompatible

namespace HolomorphicAnosov

universe u v

/-- Hatcher's straight interpolation between the identity and the radial
projection, on the original normed characteristic prism. -/
noncomputable def cw_prism_deform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : unitInterval × (Metric.closedBall (0 : E) 1 × unitInterval)) :
    Metric.closedBall (0 : E) 1 × unitInterval := by
  let s : ℝ := q.1
  let x : E := q.2.1.val
  let y : E := (cw_prism_radial q.2).1.val
  have hs0 : 0 ≤ s := q.1.property.1
  have hs1 : s ≤ 1 := q.1.property.2
  have hx : ‖x‖ ≤ 1 := by
    simpa only [x, Metric.mem_closedBall, dist_zero_right] using q.2.1.property
  have hy : ‖y‖ ≤ 1 := by
    simpa only [y, Metric.mem_closedBall, dist_zero_right] using
      (cw_prism_radial q.2).1.property
  have hnorm : ‖(1 - s) • x + s • y‖ ≤ 1 := by
    calc
      ‖(1 - s) • x + s • y‖ ≤ ‖(1 - s) • x‖ + ‖s • y‖ := norm_add_le _ _
      _ = (1 - s) * ‖x‖ + s * ‖y‖ := by
        simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0,
          abs_of_nonneg (sub_nonneg.mpr hs1)]
      _ ≤ (1 - s) * 1 + s * 1 := by gcongr
      _ = 1 := by ring
  exact (⟨(1 - s) • x + s • y,
    by simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm⟩,
    Set.Icc.convexComb q.2.2 (cw_prism_radial q.2).2 q.1)

end HolomorphicAnosov
