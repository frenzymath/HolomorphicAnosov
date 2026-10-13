import Mathlib.Analysis.Complex.UnitDisc.Basic
import Mathlib.Analysis.InnerProductSpace.Convex

open Set
open scoped ComplexConjugate
namespace HolomorphicAnosov.Analysis

/-- The supporting line of a chord between distinct unit-circle points meets
the circle only at those endpoints.

Source: elementary circle-chord geometry in Cairns (1951), §3(E)--§4(A),
pp.863--864, and Tao, *246C Notes 2*, §2 Theorem 20 (chord-cap step).
This is the boundary version of the existing unit-circle zero-determinant
calculation. Divide the displacement by the nonzero chord direction; the zero
determinant makes the quotient real. The squared norm of the resulting affine
combination equals 1-t(1-t)‖ω-ζ‖². Since all three points are on the unit circle,
t(1-t)=0, giving exactly the two endpoints. Antipodal endpoints are included. -/
theorem unit_circle_chord_boundary_zero_determinant (ζ ω z : ℂ)
    (hDistinct : ζ ≠ ω) (hζnorm : ‖ζ‖ = 1) (hωnorm : ‖ω‖ = 1)
    (hznorm : ‖z‖ = 1) (hz : (conj (ω - ζ) * (z - ζ)).im = 0) :
    z = ζ ∨ z = ω := by
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
  have hzsq : Complex.normSq z = 1 := by simp [Complex.normSq_eq_norm_sq, hznorm]
  have hidentity : Complex.normSq z =
      1 - w.re * (1 - w.re) * Complex.normSq d := by
    rw [hzline, AffineMap.lineMap_apply_module]
    simp only [Complex.normSq_apply, Complex.real_smul, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, add_zero] at hζ hω ⊢
    dsimp only [d]
    simp only [Complex.sub_re, Complex.sub_im]
    linear_combination (1 - w.re) * hζ + w.re * hω
  have hdsq : Complex.normSq d ≠ 0 := (Complex.normSq_pos.mpr hd).ne'
  have ht : w.re * (1 - w.re) = 0 := by
    apply (mul_eq_zero.mp (show w.re * (1 - w.re) * Complex.normSq d = 0 by
      linarith [hidentity, hzsq])).resolve_right hdsq
  rcases mul_eq_zero.mp ht with ht | ht
  · left
    simpa [ht] using hzline
  · right
    have ht' : w.re = 1 := by linarith
    simpa [ht'] using hzline


end HolomorphicAnosov.Analysis
