import Mathlib.Analysis.Complex.Circle

namespace HolomorphicAnosov
open Set Complex

/-- A nonzero side coefficient has an explicit strict interior direction.

Source: Cairns (1951), §4(A), pp.863--864.  If `d = E₂ - E₁` and
`c = im (star d * (Eₚ - E₁))`, then the unit direction obtained by normalizing
`c * I * d` satisfies `c * im (star d * v) > 0`.  This isolates the strict
semicircle witness used to make the radial-star set nonempty. -/
theorem cairns_normalized_interior_direction
    (E₁ E₂ Eₚ : ℂ)
    (hE : E₁ ≠ E₂)
    (hSide : (star (E₂ - E₁) * (Eₚ - E₁)).im ≠ 0) :
    ∃ v : Circle, 0 <
      (star (E₂ - E₁) * (Eₚ - E₁)).im *
        (star (E₂ - E₁) * (v : ℂ)).im := by
  let d : ℂ := E₂ - E₁
  let c : ℝ := (star d * (Eₚ - E₁)).im
  have hd : d ≠ 0 := by
    dsimp [d]
    exact sub_ne_zero.mpr hE.symm
  have hc : c ≠ 0 := by
    dsimp [c]
    exact hSide
  let x : ℂ := (c : ℂ) * I * d
  have hx : x ≠ 0 := by
    dsimp [x]
    exact mul_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr hc) I_ne_zero) hd
  have hxnorm : ‖x / ‖x‖‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
    exact div_self (ne_of_gt (norm_pos_iff.mpr hx))
  let v : Circle := ⟨x / ‖x‖, by
    simpa [Submonoid.unitSphere, mem_sphere_zero_iff_norm] using hxnorm⟩
  refine ⟨v, ?_⟩
  have hprod : star d * x = (c * Complex.normSq d : ℂ) * I := by
    dsimp [x]
    rw [Complex.normSq_apply]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    <;> ring
  have hvprod : star d * (v : ℂ) = ((c * Complex.normSq d : ℂ) * I) / ‖x‖ := by
    change star d * (x / ‖x‖) = _
    rw [div_eq_mul_inv, ← mul_assoc, hprod, div_eq_mul_inv]
  have him : (star d * (v : ℂ)).im = c * Complex.normSq d / ‖x‖ := by
    rw [hvprod, Complex.div_im]
    simp [Complex.mul_re, Complex.mul_im]
    field_simp
  rw [show (star (E₂ - E₁) * (Eₚ - E₁)).im = c by rfl,
    show star (E₂ - E₁) * (v : ℂ) = star d * (v : ℂ) by rfl, him]
  have hnormsq : 0 < Complex.normSq d := Complex.normSq_pos.mpr hd
  have hnormx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hcc : 0 < c * c := mul_self_pos.mpr hc
  have hp := div_pos (mul_pos hcc hnormsq) hnormx
  convert hp using 1; ring

end HolomorphicAnosov
