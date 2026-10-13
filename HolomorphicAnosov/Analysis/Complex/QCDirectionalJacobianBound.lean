import HolomorphicAnosov.Analysis.Complex.QCRealLinearArea
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.Determinant

namespace HolomorphicAnosov

/-- Source: Lehto–Virtanen I.Theorem 3.1, p.18, the pointwise Jacobian
bound underlying (3.4). Take the preimage of the quarter-turn of `A 1` and
normalize it. Directional distortion bounds its norm by `K`; the preceding
area identity then gives the bound without choosing singular-value extrema. -/
theorem qc_directional_jacobian_bound (A : ℂ ≃L[ℝ] ℂ) {K : ℝ}
    (hdet : 0 < (A : ℂ →L[ℝ] ℂ).det)
    (hK : ∀ v w : ℂ, ‖v‖ = 1 → ‖w‖ = 1 → ‖A v‖ ≤ K * ‖A w‖) :
    ‖A 1‖ ^ 2 ≤ K * (A : ℂ →L[ℝ] ℂ).det := by
  let v := A.symm (Complex.I * A 1)
  have hu : A 1 ≠ 0 := by
    intro h
    have he : (1 : ℂ) = 0 := A.injective (h.trans A.map_zero.symm)
    exact one_ne_zero he
  have hu_norm : 0 < ‖A 1‖ := norm_pos_iff.mpr hu
  have hv : v ≠ 0 := by
    intro h
    have he := congrArg A h
    simp only [v, A.apply_symm_apply, map_zero, mul_eq_zero, Complex.I_ne_zero,
      false_or] at he
    exact hu he
  have hv_norm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hunit : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hv_norm.ne']
  have hdist := hK 1 ((‖v‖⁻¹ : ℝ) • v) (by simp) hunit
  have hAv : A v = Complex.I * A 1 := A.apply_symm_apply _
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, hAv,
    norm_mul, Complex.norm_I, one_mul] at hdist
  have hvK : ‖v‖ ≤ K := by
    have hmul := mul_le_mul_of_nonneg_right hdist (norm_nonneg v)
    have hc : K * (‖v‖⁻¹ * ‖A 1‖) * ‖v‖ = K * ‖A 1‖ := by
      field_simp
    rw [hc] at hmul
    nlinarith
  have harea := qc_real_linear_area (A : ℂ →L[ℝ] ℂ) v
  rw [show (A : ℂ →L[ℝ] ℂ) v = Complex.I * A 1 from hAv] at harea
  have hnormarea : (starRingEnd ℂ (A 1) * (Complex.I * A 1)).im = ‖A 1‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  change (starRingEnd ℂ (A 1) * (Complex.I * A 1)).im =
    (A : ℂ →L[ℝ] ℂ).det * v.im at harea
  rw [hnormarea] at harea
  calc
    ‖A 1‖ ^ 2 = (A : ℂ →L[ℝ] ℂ).det * v.im := harea
    _ ≤ (A : ℂ →L[ℝ] ℂ).det * K :=
      mul_le_mul_of_nonneg_left ((Complex.im_le_norm v).trans hvK) hdet.le
    _ = K * (A : ℂ →L[ℝ] ℂ).det := mul_comm _ _


end HolomorphicAnosov
