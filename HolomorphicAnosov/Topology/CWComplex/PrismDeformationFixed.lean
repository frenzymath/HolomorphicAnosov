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
import HolomorphicAnosov.Topology.CWComplex.PrismDeformation
import HolomorphicAnosov.Topology.CWComplex.ContinuousPrismDeformation
import HolomorphicAnosov.Topology.CWComplex.PrismDeformationZero
import HolomorphicAnosov.Topology.CWComplex.PrismDeformationOne

namespace HolomorphicAnosov

universe u v

/-- Every fixed point of the radial projection remains fixed throughout the
straight interpolation. -/
theorem cw_prism_deform_fixed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Metric.closedBall (0 : E) 1 × unitInterval)
    (hp : cw_prism_radial p = p) (s : unitInterval) :
    cw_prism_deform (s, p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    have hx : (cw_prism_radial p).1.val = p.1.val := congrArg (fun q ↦ q.1.val) hp
    simp [cw_prism_deform, hx, sub_smul]
  · have hu : (cw_prism_radial p).2 = p.2 := congrArg Prod.snd hp
    simp [cw_prism_deform, hu]

end HolomorphicAnosov
