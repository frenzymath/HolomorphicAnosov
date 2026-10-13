import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality

open MeasureTheory Set

namespace HolomorphicAnosov.Analysis

/-- The central elliptic kernel is integrable up to its square-root endpoint.
Agent completion of the integrability detail omitted in Whittaker–Watson §22.32,
p.501. Mathlib's integrable inverse semicircle
kernel absorbs the singular factor, while the second inverse radical is continuous
on the closed unit interval because its radicand is at least `1-c²>0`. -/
theorem whittakerWatsonCentralIntegrable (c : ℝ) (hc : c ^ 2 < 1) :
    IntervalIntegrable (fun t : ℝ ↦ if 0 < t ∧ t < 1 then
      1 / (Real.sqrt (1 - t ^ 2) * Real.sqrt (1 - c ^ 2 * t ^ 2)) else 0)
      volume 0 1 := by
  have hbase : IntervalIntegrable (fun t : ℝ ↦ (Real.sqrt (1 - t ^ 2))⁻¹)
      volume 0 1 := by
    simpa only [Real.sqrt_inv] using
      (Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv.mono_set
        (c := (0 : ℝ)) (d := 1) (by
      simp only [Set.uIcc_of_le (show (-1 : ℝ) ≤ 1 by norm_num),
        Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
      exact Set.Icc_subset_Icc (by norm_num) le_rfl))
  have hpos : ∀ t ∈ Set.uIcc (0 : ℝ) 1, 0 < 1 - c ^ 2 * t ^ 2 := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    nlinarith [mul_le_mul_of_nonneg_left ht2 (sq_nonneg c)]
  have hcont : ContinuousOn (fun t : ℝ ↦ (Real.sqrt (1 - c ^ 2 * t ^ 2))⁻¹)
      (Set.uIcc 0 1) := by
    apply ContinuousOn.inv₀
    · fun_prop
    · exact fun t ht ↦ (Real.sqrt_pos.2 (hpos t ht)).ne'
  apply (hbase.mul_continuousOn hcont).congr_uIoo
  intro t ht
  rw [Set.uIoo_of_le zero_le_one] at ht
  simp [ht.1, ht.2, one_div, mul_comm]

end HolomorphicAnosov.Analysis
