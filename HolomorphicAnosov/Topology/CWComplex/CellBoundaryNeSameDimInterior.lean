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

namespace HolomorphicAnosov

universe u v

/-- A boundary point of an n-cell cannot coincide with an interior point of
another n-cell, since its image is in the lower skeleton. -/
theorem cw_cell_boundary_ne_same_dim_interior
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (n : ℕ) (i j : Topology.RelCWComplex.cell (Set.univ : Set X) n)
    (z w : Metric.closedBall (0 : Fin n → ℝ) 1)
    (hz : ‖z.val‖ = 1) (hw : ‖w.val‖ < 1) :
    Topology.RelCWComplex.map n i z.val ≠ Topology.RelCWComplex.map n j w.val := by
  have hfront : Topology.RelCWComplex.map n i z.val ∈
      (Topology.CWComplex.skeletonLT (Set.univ : Set X) (n : ℕ∞) : Set X) := by
    apply Topology.CWComplex.cellFrontier_subset_skeletonLT n i
    change Topology.RelCWComplex.map n i z.val ∈
      Topology.RelCWComplex.map n i '' Metric.sphere (0 : Fin n → ℝ) 1
    exact ⟨z.val, by simpa only [Metric.mem_sphere, dist_zero_right] using hz, rfl⟩
  have hopen : Topology.RelCWComplex.map n j w.val ∈
      Topology.CWComplex.openCell n j :=
    ⟨w.val, by simpa only [Metric.mem_ball, dist_zero_right] using hw, rfl⟩
  intro heq
  exact (Set.disjoint_left.mp (Topology.CWComplex.disjoint_skeletonLT_openCell
    (show (n : ℕ∞) ≤ n from le_refl _))) hfront (heq.symm ▸ hopen)

end HolomorphicAnosov
