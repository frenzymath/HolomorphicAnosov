import Mathlib.Analysis.Complex.UnitDisc.Basic
open scoped ComplexConjugate
namespace HolomorphicAnosov.Analysis
/-- Reversing the oriented chord endpoints negates the strict determinant functional. -/
theorem chord_cap_sign_reversal (ζ ω z : ℂ) :
    (conj (ζ - ω) * (z - ω)).im = -(conj (ω - ζ) * (z - ζ)).im := by
  rw [show ζ - ω = -(ω - ζ) by ring, map_neg, neg_mul]
  simp only [Complex.neg_im, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.conj_re, Complex.conj_im]
  ring
end HolomorphicAnosov.Analysis
