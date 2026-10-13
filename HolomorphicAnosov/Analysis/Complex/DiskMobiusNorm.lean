import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open scoped ComplexConjugate

namespace HolomorphicAnosov

/-- The disk Möbius norm identity used in step 4 of the omitted-values estimate.
Source: Lyubich, *Conformal Geometry and Dynamics of Quadratic Polynomials*,
§7.1, p. 133, disk automorphisms. Expand squared complex norms into real and
imaginary parts; the difference of the denominator and numerator squared norms
is `(1 - ‖v‖²) * (1 - ‖w‖²)`. Divide by the nonzero denominator squared norm. -/
theorem diskMobius_norm_identity (v w : ℂ) (h : 1 - conj v * w ≠ 0) :
    1 - ‖(w - v) / (1 - conj v * w)‖ ^ 2 =
      ((1 - ‖v‖ ^ 2) * (1 - ‖w‖ ^ 2)) / ‖1 - conj v * w‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_div]
  have hn : Complex.normSq (1 - conj v * w) ≠ 0 :=
    by simpa only [Complex.normSq_eq_norm_sq] using
      pow_ne_zero 2 (norm_ne_zero_iff.mpr h)
  apply (eq_div_iff hn).2
  rw [sub_mul, one_mul, div_mul_cancel₀ _ hn]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  ring

end HolomorphicAnosov

