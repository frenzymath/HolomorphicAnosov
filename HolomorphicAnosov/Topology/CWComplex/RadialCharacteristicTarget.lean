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

namespace HolomorphicAnosov

universe u v

/-- Every projected characteristic point is on the bottom or lies over the
original lower skeleton, with no regular-cell assumption. -/
theorem cw_prism_radial_characteristic_target
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (n : ℕ) (i : Topology.RelCWComplex.cell (Set.univ : Set X) n)
    (p : Metric.closedBall (0 : Fin n → ℝ) 1 × unitInterval) :
    (cw_prism_radial p).2 = 0 ∨
    Topology.RelCWComplex.map n i (cw_prism_radial p).1.val ∈
      (Topology.CWComplex.skeletonLT (Set.univ : Set X) (n : ℕ∞) : Set X) := by
  rcases cw_prism_radial_in_bottom_or_side p with hbottom | hside
  · exact Or.inl hbottom
  · refine Or.inr ?_
    apply Topology.CWComplex.cellFrontier_subset_skeletonLT n i
    change Topology.RelCWComplex.map n i (cw_prism_radial p).1.val ∈
      Topology.RelCWComplex.map n i '' Metric.sphere (0 : Fin n → ℝ) 1
    exact ⟨(cw_prism_radial p).1.val,
      by simpa only [Metric.mem_sphere, dist_zero_right] using hside, rfl⟩

end HolomorphicAnosov
