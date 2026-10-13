import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace HolomorphicAnosov

/-- Taking a derivative lowers a finite Hölder order by one without increasing
any of the jet or Hölder constants.

Source: de la Llave–Obaya, Definitions 2.1/2.5 and the derivative-norm recursion
used in Theorem 4.3(ii.3), pp.169–170. The operator targets have the original norms.
The right-currying linear isometry identifies every jth derivative of Df with
the (j+1)th derivative of f, including differences at two points. Thus the
supplied bounds transfer unchanged. The C^n certificate follows from the
open-set derivative criterion. No derivative of order n+2 is used. -/
theorem fderiv_holder_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : Set E) (hS : IsOpen S) (n : ℕ) (f : E → F)
    (hf : ContDiffOn ℝ (n + 1) f S) (A α : ℝ)
    (hfnorm : ∀ j : ℕ, j ≤ n + 1 → ∀ x ∈ S, ‖iteratedFDeriv ℝ j f x‖ ≤ A)
    (hfholder : ∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ (n + 1) f x - iteratedFDeriv ℝ (n + 1) f y‖ ≤
        A * ‖x - y‖ ^ α) :
    ContDiffOn ℝ n (fderiv ℝ f) S ∧
      (∀ j : ℕ, j ≤ n → ∀ x ∈ S, ‖iteratedFDeriv ℝ j (fderiv ℝ f) x‖ ≤ A) ∧
      (∀ x ∈ S, ∀ y ∈ S,
        ‖iteratedFDeriv ℝ n (fderiv ℝ f) x - iteratedFDeriv ℝ n (fderiv ℝ f) y‖ ≤
          A * ‖x - y‖ ^ α) := by
  refine ⟨hf.fderiv_of_isOpen hS (by simp), ?_, ?_⟩
  · intro j hj x hx
    rw [norm_iteratedFDeriv_fderiv]
    exact hfnorm (j + 1) (by omega) x hx
  · intro x hx y hy
    have h := hfholder x hx y hy
    rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right] at h
    simpa only [Function.comp_apply, ← LinearIsometryEquiv.map_sub,
      LinearIsometryEquiv.norm_map] using h


end HolomorphicAnosov
