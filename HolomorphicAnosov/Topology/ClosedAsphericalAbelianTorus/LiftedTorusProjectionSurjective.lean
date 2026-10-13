import HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus.LiftedTorusProjection
import Mathlib.Topology.Instances.AddCircle.Real

/-!
Public reusable helper extracted from `HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus`.
Source: Ghys, *Holomorphic Anosov systems* (1995), proof of Theorem B, p.598;
expanded with the cited Hatcher results recorded in the parent module.
-/

namespace HolomorphicAnosov

universe u v

open scoped ContDiff

theorem liftedTorusProjection_surjective (r : ℕ) :
    Function.Surjective (liftedTorusProjection.{u} r) := by
  intro x
  choose y hy using fun i : Fin r ↦ QuotientAddGroup.mk_surjective (x.down i)
  refine ⟨(EuclideanSpace.equiv (Fin r) ℝ).symm y, ?_⟩
  apply ULift.ext
  funext i
  exact hy i

end HolomorphicAnosov
