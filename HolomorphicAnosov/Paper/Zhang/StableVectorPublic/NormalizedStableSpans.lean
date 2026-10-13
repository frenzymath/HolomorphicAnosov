import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Complex.Basic

noncomputable section
namespace HolomorphicAnosov

/-- A normalized vector in a one-dimensional stable subspace is nonzero and spans that subspace.
(Zhang, Lemma 4.3) -/
theorem normalized_stable_spans {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S : Submodule ℂ V) (θ : V →ₗ[ℂ] ℂ) (e : V)
    (hrank : Module.finrank ℂ S = 1) (he : e ∈ S) (hθe : θ e = 1) :
    e ≠ 0 ∧ S = Submodule.span ℂ ({e} : Set V) := by
  have hne : e ≠ 0 := by
    intro h
    simp [h] at hθe
  exact ⟨hne, eq_span_singleton_of_mem_of_finrank_eq_one hrank he hne⟩



end HolomorphicAnosov
