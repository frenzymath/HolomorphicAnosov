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

/-- The target keeps its actual quotient/product topology. Only a universe lift
is made, to place its singular chains in the same universe as the manifold. -/
@[instance_reducible]
noncomputable def liftedTorusChartedSpace (r : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin r)) (ULift.{u} (UnitAddTorus (Fin r))) :=
  (liftedTorusProjection_localHomeomorph r).chartedSpace
    (liftedTorusProjection_surjective r)

end HolomorphicAnosov
