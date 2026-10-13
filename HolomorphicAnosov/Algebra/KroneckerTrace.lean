import Mathlib.LinearAlgebra.Trace

noncomputable section
namespace HolomorphicAnosov

/-- Endomorphisms adjoint under a perfect pairing have equal traces.

Source: Hatcher, Algebraic Topology pp.197–198 (natural field Kronecker pairing)
and p.179 (trace in a basis). This algebraic adapter uses the given full-dual
identification to conjugate the cohomological endomorphism to the transpose of
the homological endomorphism. The pairing equation proves this equality at every
functional and every vector. Trace is invariant under linear conjugacy and
transpose. Finite dimensionality is explicitly required only on the homology
space, and is a conclusion of the torus cup-basis theorem in the application.
-/
theorem trace_eq_of_kronecker_naturality
    {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ V]
    (E : W ≃ₗ[ℚ] Module.Dual ℚ V) (f : V →ₗ[ℚ] V) (g : W →ₗ[ℚ] W)
    (h : ∀ a x, E (g a) x = E a (f x)) :
    LinearMap.trace ℚ W g = LinearMap.trace ℚ V f := by
  have he : E.conj g = Module.Dual.transpose f := by
    ext a x
    change E (g (E.symm a)) x = a (f x)
    rw [h, E.apply_symm_apply]
  calc
    LinearMap.trace ℚ W g = LinearMap.trace ℚ (Module.Dual ℚ V) (E.conj g) :=
      (LinearMap.trace_conj' g E).symm
    _ = LinearMap.trace ℚ V f := by
      rw [he]
      exact LinearMap.congr_fun (LinearMap.trace_transpose ℚ V) f

end HolomorphicAnosov
