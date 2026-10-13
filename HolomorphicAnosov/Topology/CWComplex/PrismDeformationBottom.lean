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
import HolomorphicAnosov.Topology.CWComplex.PrismDeformationFixed

namespace HolomorphicAnosov

universe u v

/-- The local deformation fixes the bottom at every deformation time. -/
theorem cw_prism_deform_bottom
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : unitInterval) (x : Metric.closedBall (0 : E) 1) :
    cw_prism_deform (s, (x, 0)) = (x, 0) :=
  cw_prism_deform_fixed (x, 0) (cw_prism_radial_bottom x) s

end HolomorphicAnosov
