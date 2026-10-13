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
import HolomorphicAnosov.Topology.CWComplex.PrismDeformationBottom
import HolomorphicAnosov.Topology.CWComplex.PrismDeformationSide
import HolomorphicAnosov.Topology.CWComplex.PrismDeformationSameDimCompatible
import HolomorphicAnosov.Topology.CWComplex.CellInLowerSkeletonBoundary
import HolomorphicAnosov.Topology.CWComplex.CellInSubcomplexBoundary

namespace HolomorphicAnosov

universe u v

/-- The n-cell deformation agrees with the identity formula on any lower
cell representative identified with its frontier. -/
theorem cw_prism_deform_lower_cell_compatible
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (n m : ℕ) (i : Topology.RelCWComplex.cell (Set.univ : Set X) n)
    (j : Topology.RelCWComplex.cell (Set.univ : Set X) m)
    (z : Metric.closedBall (0 : Fin n → ℝ) 1)
    (w : Metric.closedBall (0 : Fin m → ℝ) 1)
    (s t : unitInterval)
    (hz : Topology.RelCWComplex.map n i z.val ∈
      (Topology.CWComplex.skeletonLT (Set.univ : Set X) (n : ℕ∞) : Set X))
    (heq : Topology.RelCWComplex.map n i z.val =
      Topology.RelCWComplex.map m j w.val) :
    (Topology.RelCWComplex.map n i (cw_prism_deform (s, (z, t))).1.val,
      (cw_prism_deform (s, (z, t))).2) =
      (Topology.RelCWComplex.map m j w.val, t) := by
  have hboundary := cw_cell_in_lower_skeleton_is_boundary n i z hz
  rw [cw_prism_deform_side s z t hboundary]
  simp [heq]

end HolomorphicAnosov
