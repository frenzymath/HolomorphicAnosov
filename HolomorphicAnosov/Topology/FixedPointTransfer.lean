import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Homotopy.Path

universe u v w
noncomputable section
namespace HolomorphicAnosov.Topology

/-- A fixed point of a conjugate lift transfers through a homeomorphism, together
with the downstairs lift equation.

Source context: Franks (1969), Corollary 1.3, p.119. The formulation for
an arbitrary homeomorphism is an agent-written algebraic generalization.
Put ξ = Q.symm v. The inverse identity and the hypothesis give
Q(F(ξ)) = v = Q(ξ), hence F(ξ) = ξ by injectivity of Q. Evaluate the
lift equation at ξ and substitute this fixed-point equality to obtain
f^[m](p(ξ)) = p(ξ). This proves both conclusions with the same witness.
The argument also applies at m = 0 and uses no topology on M. -/
theorem fixed_point_transfer_homeomorph
    {V : Type u} {E : Type v} {M : Type w} [TopologicalSpace V] [TopologicalSpace E]
    (Q : E ≃ₜ V) (p : E → M) (f : M → M) (m : ℕ)
    (F : C(E, E))
    (hF : ∀ ξ, p (F ξ) = f^[m] (p ξ))
    (v : V)
    (hv : Q (F (Q.symm v)) = v) :
    ∃ ξ, F ξ = ξ ∧ f^[m] (p ξ) = p ξ := by
  refine ⟨Q.symm v, ?_, ?_⟩
  · exact Q.injective (hv.trans (Q.apply_symm_apply v).symm)
  · have heq : F (Q.symm v) = Q.symm v :=
      Q.injective (hv.trans (Q.apply_symm_apply v).symm)
    simpa only [heq] using (hF (Q.symm v)).symm

end HolomorphicAnosov.Topology
