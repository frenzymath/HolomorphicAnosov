import HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus.LiftedTorusProjection
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Geometry.Manifold.Instances.Real

/-!
Public reusable helper extracted from `HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus`.
Source: Ghys, *Holomorphic Anosov systems* (1995), proof of Theorem B, p.598;
expanded with the cited Hatcher results recorded in the parent module.
-/

namespace HolomorphicAnosov

universe u v

open scoped ContDiff

theorem liftedTorusProjection_localHomeomorph (r : ℕ) :
    IsLocalHomeomorph (liftedTorusProjection.{u} r) := by
  classical
  have hpi : IsLocalHomeomorph (fun a : Fin r → ℝ ↦ fun i ↦ (a i : UnitAddCircle)) := by
    intro a
    choose e he heq using fun i : Fin r ↦ AddCircle.isLocalHomeomorph_coe (1 : ℝ) (a i)
    refine ⟨OpenPartialHomeomorph.pi e, (fun i _ ↦ he i), ?_⟩
    funext x i
    exact congrFun (heq i) (x i)
  exact Homeomorph.ulift.symm.isLocalHomeomorph.comp
    (hpi.comp (EuclideanSpace.equiv (Fin r) ℝ).toHomeomorph.isLocalHomeomorph)

end HolomorphicAnosov
