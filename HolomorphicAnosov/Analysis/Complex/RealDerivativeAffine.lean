import Mathlib.Analysis.Complex.OpenMapping

/-!
Source: Farb–Margalit, *A Primer on Mapping Class Groups*, Version 5.0,
§11.5, Theorem 11.10, printed p.343.  The statement records the omitted
constant-slope analytic step in the `K = 1` equality argument.  The proof
follows the standard argument: the derivative is analytic, the hypothesis on
its imaginary part makes it constant by the open mapping theorem, and the
equal-derivative theorem then gives an affine expression for `f`.
-/

namespace HolomorphicAnosov.Analysis.Complex

/-- A holomorphic map whose complex derivative is real-valued is affine over
the real scalars on a connected open set.

The derivative is analytic and has constant imaginary part, hence is constant.
Its value is real by evaluation at a point of the nonempty domain. Comparing
with the corresponding linear map gives the additive constant. -/
theorem real_affine_of_deriv_im_eq_zero {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hc : IsConnected U) (hf : DifferentiableOn ℂ f U)
    (hreal : ∀ z ∈ U, (deriv f z).im = 0) :
    ∃ (c : ℝ) (d : ℂ), ∀ z ∈ U, f z = (c : ℂ) * z + d := by
  obtain ⟨q, hq⟩ := ((hf.deriv hU).analyticOnNhd hU).eq_const_of_im_eq_const
    hreal hU hc
  obtain ⟨z₀, hz₀⟩ := hc.nonempty
  have hqim : q.im = 0 := by
    rw [← hq z₀ hz₀]
    exact hreal z₀ hz₀
  have hqreal : q = (q.re : ℂ) := by
    apply Complex.ext <;> simp [hqim]
  obtain ⟨d, hd⟩ := hU.exists_eq_add_of_deriv_eq hc.isPreconnected hf
    ((differentiable_const q).mul differentiable_id).differentiableOn
    (show Set.EqOn (deriv f) (deriv (fun z : ℂ ↦ q * z)) U from by
      intro z hz
      simpa only [deriv_const_mul_id] using hq z hz)
  refine ⟨q.re, d, fun z hz ↦ ?_⟩
  rw [← hqreal]
  exact hd hz

end HolomorphicAnosov.Analysis.Complex
