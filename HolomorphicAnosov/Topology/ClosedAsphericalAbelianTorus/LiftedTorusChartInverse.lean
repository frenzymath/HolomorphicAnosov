import HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus.LiftedTorusChartedSpace
import HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus.LiftedTorusProjection
import HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus.LiftedTorusProjectionLocalHomeomorph
import HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus.LiftedTorusProjectionSurjective
import Mathlib.Geometry.Manifold.Instances.Real

/-!
Public reusable helper extracted from `HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus`.
Source: Ghys, *Holomorphic Anosov systems* (1995), proof of Theorem B, p.598;
expanded with the cited Hatcher results recorded in the parent module.
-/

namespace HolomorphicAnosov

universe u v

open scoped ContDiff

theorem liftedTorus_chart_inverse (r : ℕ)
    (e : OpenPartialHomeomorph (ULift.{u} (UnitAddTorus (Fin r)))
      (EuclideanSpace ℝ (Fin r))) :
    letI := liftedTorusChartedSpace.{u} r
    e ∈ atlas (EuclideanSpace ℝ (Fin r)) (ULift.{u} (UnitAddTorus (Fin r))) →
      (e.symm : EuclideanSpace ℝ (Fin r) → ULift.{u} (UnitAddTorus (Fin r))) =
        liftedTorusProjection r := by
  intro he
  change ∃ x : ULift.{u} (UnitAddTorus (Fin r)),
    ((liftedTorusProjection_localHomeomorph r).localInverseAt
      ((liftedTorusProjection_surjective r).hasRightInverse.choose x)).trans
        (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin r))) = e at he
  obtain ⟨x, rfl⟩ := he
  simp

end HolomorphicAnosov
