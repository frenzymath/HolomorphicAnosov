import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.Instances.AddCircle.Real

/-!
Public reusable helper extracted from `HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus`.
Source: Ghys, *Holomorphic Anosov systems* (1995), proof of Theorem B, p.598;
expanded with the cited Hatcher results recorded in the parent module.
-/

namespace HolomorphicAnosov

universe u v

open scoped ContDiff

def liftedTorusProjection (r : ℕ) :
    EuclideanSpace ℝ (Fin r) → ULift.{u} (UnitAddTorus (Fin r)) :=
  fun x ↦ ⟨fun i ↦ (x i : UnitAddCircle)⟩

end HolomorphicAnosov
