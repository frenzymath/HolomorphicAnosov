import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Homotopy.Path

universe u v w x
noncomputable section
namespace HolomorphicAnosov.Topology

/-- A continuous lift on a pullback coordinate model lifts the iterated
conjugated downstairs map under the coordinate projection. -/
theorem pullback_coordinate_lift_identity_homeomorph
    {V : Type u} {E : Type v} {M : Type w} {X : Type x}
    [TopologicalSpace V] [TopologicalSpace E] [TopologicalSpace M] [TopologicalSpace X]
    (Q : E ≃ₜ V) (q : M ≃ₜ X) (p : E → M) (proj : V → X)
    (hQ : ∀ ξ, proj (Q ξ) = q (p ξ))
    (f : M → M) (m : ℕ) (F : C(E, E))
    (hF : ∀ ξ, p (F ξ) = f^[m] (p ξ)) (v : V) :
    proj (Q (F (Q.symm v))) =
      (fun x ↦ q (f (q.symm x)))^[m] (proj v) := by
  have hsemi : Function.Semiconj q f (fun x ↦ q (f (q.symm x))) := by
    intro x
    simp
  have h := hQ (F (Q.symm v))
  rw [hF] at h
  rw [hsemi.iterate_right m (p (Q.symm v))] at h
  rw [← hQ (Q.symm v)] at h
  simpa only [Q.apply_symm_apply] using h

end HolomorphicAnosov.Topology
