import Mathlib.Analysis.Complex.UnitDisc.Basic
import Mathlib.Analysis.InnerProductSpace.Convex

open Set
open scoped ComplexConjugate
namespace HolomorphicAnosov.Analysis

/-- An interior point on the supporting line of a unit-circle chord lies on its
open segment. Source: the elementary chord geometry in Tao, *246C Notes 2*,
§2, Theorem 20, final paragraph. Agent-written algebraic expansion: divide the
point displacement by the nonzero endpoint difference. The determinant
hypothesis makes this quotient real. Writing its real part as t expresses the
point as the affine combination. The identity
‖(1-t)ζ+tω‖² = 1-t(1-t)‖ω-ζ‖² and the strict interior norm bound imply
0<t<1. The argument includes antipodal endpoints. -/
theorem unit_circle_chord_zero_determinant (ζ ω z : ℂ) (hDistinct : ζ ≠ ω) (hζnorm : ‖ζ‖ = 1) (hωnorm : ‖ω‖ = 1) (hznorm : ‖z‖ < 1)
    (hz : (conj (ω - ζ) * (z - ζ)).im = 0) :
    ∃ t : ℝ, t ∈ Ioo 0 1 ∧ z = AffineMap.lineMap ζ ω t := by
  let d : ℂ := ω - ζ
  have hd : d ≠ 0 := by
    intro h
    exact hDistinct (sub_eq_zero.mp h).symm
  let w : ℂ := (z - ζ) / d
  have hwim : w.im = 0 := by
    dsimp [w]
    rw [Complex.div_im]
    have hnum : (z - ζ).im * d.re - (z - ζ).re * d.im = 0 := by
      change (d.re * (z - ζ).im + -d.im * (z - ζ).re) = 0 at hz
      nlinarith
    rw [← sub_div, hnum, zero_div]
  have hwreal : (w.re : ℂ) = w := by
    apply Complex.ext
    · simp
    · simpa using hwim.symm
  have hzline : z = AffineMap.lineMap ζ ω w.re := by
    rw [AffineMap.lineMap_apply_module]
    simp only [Complex.real_smul]
    push_cast
    rw [hwreal]
    change z = (1 - (z - ζ) / d) * ζ + ((z - ζ) / d) * ω
    field_simp
    dsimp [d]
    ring
  have hζ : Complex.normSq ζ = 1 := by simp [Complex.normSq_eq_norm_sq, hζnorm]
  have hω : Complex.normSq ω = 1 := by simp [Complex.normSq_eq_norm_sq, hωnorm]
  have hzsq : Complex.normSq z < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hznorm, norm_nonneg z]
  have hidentity : Complex.normSq z =
      1 - w.re * (1 - w.re) * Complex.normSq d := by
    rw [hzline, AffineMap.lineMap_apply_module]
    simp only [Complex.normSq_apply, Complex.real_smul, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, add_zero] at hζ hω ⊢
    dsimp only [d]
    simp only [Complex.sub_re, Complex.sub_im]
    linear_combination (1 - w.re) * hζ + w.re * hω
  have hprod : 0 < w.re * (1 - w.re) := by
    have hdsq : 0 ≤ Complex.normSq d := Complex.normSq_nonneg d
    nlinarith
  refine ⟨w.re, ⟨?_, ?_⟩, hzline⟩ <;> nlinarith [sq_nonneg w.re]

end HolomorphicAnosov.Analysis
