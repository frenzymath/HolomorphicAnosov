import Mathlib.Analysis.Complex.Basic

namespace HolomorphicAnosov

/-- The differential form of conformal invariance of directional distortion,
Lehto–Virtanen I.§3.3, p.17. Normalize the input similarity by its positive
stretch, apply the distortion bound to the resulting unit vectors, and cancel
the input stretch. The output stretch multiplies both sides equally. Zero
similarities also satisfy the displayed inequality directly. -/
theorem qc_similarity_distortion (A : ℂ →L[ℝ] ℂ) {K : ℝ}
    (hK : ∀ v w : ℂ, ‖v‖ = 1 → ‖w‖ = 1 → ‖A v‖ ≤ K * ‖A w‖)
    (a b : ℂ) {v w : ℂ} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ‖a * A (b * v)‖ ≤ K * ‖a * A (b * w)‖ := by
  by_cases hb : b = 0
  · simp [hb]
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hunit (z : ℂ) (hz : ‖z‖ = 1) : ‖(‖b‖⁻¹ : ℝ) • (b * z)‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, norm_mul, hz, mul_one,
      inv_mul_cancel₀ hbpos.ne']
  have h := hK ((‖b‖⁻¹ : ℝ) • (b * v)) ((‖b‖⁻¹ : ℝ) • (b * w))
    (hunit v hv) (hunit w hw)
  simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm] at h
  have h' : ‖A (b * v)‖ ≤ K * ‖A (b * w)‖ := by
    refine le_of_mul_le_mul_left ?_ (inv_pos.mpr hbpos)
    calc
      ‖b‖⁻¹ * ‖A (b * v)‖ ≤ K * (‖b‖⁻¹ * ‖A (b * w)‖) := h
      _ = ‖b‖⁻¹ * (K * ‖A (b * w)‖) := by ring
  simpa only [norm_mul, mul_left_comm K ‖a‖] using
    mul_le_mul_of_nonneg_left h' (norm_nonneg a)

end HolomorphicAnosov
