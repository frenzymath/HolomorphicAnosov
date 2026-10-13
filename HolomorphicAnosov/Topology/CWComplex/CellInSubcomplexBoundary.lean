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

namespace HolomorphicAnosov

universe u v

/-- A characteristic point of a cell not selected by a subcomplex can lie in
that subcomplex only on the characteristic sphere. Source: Hatcher,
Proposition 0.16, p.15, the overlap between a deformed cell and the fixed
subcomplex. An interior representative would belong to the cell's open cell,
which is disjoint from the subcomplex by its selected-index condition. -/
theorem cw_cell_in_subcomplex_is_boundary
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (B : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (n : ℕ) (i : Topology.RelCWComplex.cell (Set.univ : Set X) n)
    (hi : i ∉ B.I n)
    (z : Metric.closedBall (0 : Fin n → ℝ) 1)
    (h : Topology.RelCWComplex.map n i z.val ∈ (B : Set X)) :
    ‖z.val‖ = 1 := by
  have hzle : ‖z.val‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
  apply le_antisymm hzle
  by_contra hn
  have hz : ‖z.val‖ < 1 := lt_of_not_ge hn
  have hopen : Topology.RelCWComplex.map n i z.val ∈
      Topology.CWComplex.openCell n i :=
    ⟨z.val, by simpa only [Metric.mem_ball, dist_zero_right] using hz, rfl⟩
  exact (Set.disjoint_left.mp (B.disjoint_openCell_subcomplex_of_not_mem hi)) hopen h

end HolomorphicAnosov
