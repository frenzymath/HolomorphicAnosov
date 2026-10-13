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

namespace HolomorphicAnosov

universe u v

/-- At every deformation time, the local formula respects n-cell
characteristic identifications, including multiple boundary representatives. -/
theorem cw_prism_deform_same_dim_compatible
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (n : ℕ) (i j : Topology.RelCWComplex.cell (Set.univ : Set X) n)
    (z w : Metric.closedBall (0 : Fin n → ℝ) 1) (s t : unitInterval)
    (heq : Topology.RelCWComplex.map n i z.val =
      Topology.RelCWComplex.map n j w.val) :
    (Topology.RelCWComplex.map n i (cw_prism_deform (s, (z, t))).1.val,
      (cw_prism_deform (s, (z, t))).2) =
    (Topology.RelCWComplex.map n j (cw_prism_deform (s, (w, t))).1.val,
      (cw_prism_deform (s, (w, t))).2) := by
  have hzle : ‖z.val‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
  have hwle : ‖w.val‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using w.property
  by_cases hz : ‖z.val‖ < 1
  · have hw : ‖w.val‖ < 1 := by
      by_contra hn
      have hw1 : ‖w.val‖ = 1 := le_antisymm hwle (le_of_not_gt hn)
      exact cw_cell_boundary_ne_same_dim_interior n j i w z hw1 hz heq.symm
    have hij : i = j := by
      have hni : ¬ Disjoint (Topology.CWComplex.openCell n i)
          (Topology.CWComplex.openCell n j) := Set.not_disjoint_iff.mpr
        ⟨Topology.RelCWComplex.map n i z.val,
          ⟨z.val, by simpa only [Metric.mem_ball, dist_zero_right] using hz, rfl⟩,
          ⟨w.val, by simpa only [Metric.mem_ball, dist_zero_right] using hw, heq.symm⟩⟩
      have hs := Topology.CWComplex.eq_of_not_disjoint_openCell hni
      exact eq_of_heq (Sigma.mk.inj_iff.mp hs).2
    subst j
    have hzw : z = w := Subtype.ext ((Topology.RelCWComplex.map n i).injOn
      (by rw [Topology.RelCWComplex.source_eq]
          simpa only [Metric.mem_ball, dist_zero_right] using hz)
      (by rw [Topology.RelCWComplex.source_eq]
          simpa only [Metric.mem_ball, dist_zero_right] using hw) heq)
    rw [hzw]
  · have hz1 : ‖z.val‖ = 1 := le_antisymm hzle (le_of_not_gt hz)
    have hw1 : ‖w.val‖ = 1 := by
      by_contra hn
      have hw : ‖w.val‖ < 1 := lt_of_le_of_ne hwle hn
      exact cw_cell_boundary_ne_same_dim_interior n i j z w hz1 hw heq
    rw [cw_prism_deform_side s z t hz1, cw_prism_deform_side s w t hw1]
    simp [heq]

end HolomorphicAnosov
