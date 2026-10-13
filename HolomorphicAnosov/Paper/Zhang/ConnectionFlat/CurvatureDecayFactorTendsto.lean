import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

noncomputable section
universe u
namespace HolomorphicAnosov
namespace ConnectionFlatEstimates

/-- The geometric curvature decay factor tends to zero for `d ≥ 3` and `rate > 1`. (Zhang, eq. (11)) -/
theorem curvature_decay_factor_tendsto {d : ℕ} (hd : 3 ≤ d) {rate : ℝ} (hrate : 1 < rate)
    (C volume : ℝ) :
    Filter.Tendsto (fun n : ℕ ↦ C * ((rate ^ (2 * (d - 2)))⁻¹) ^ n * volume)
      Filter.atTop (nhds 0) := by
  have hbase : 1 < rate ^ (2 * (d - 2)) := one_lt_pow₀ hrate (by omega)
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one
    (inv_nonneg.mpr (pow_nonneg (by linarith : 0 ≤ rate) _))
    (inv_lt_one_of_one_lt₀ hbase)
  simpa only [mul_zero, zero_mul] using (hlim.const_mul C).mul_const volume

end ConnectionFlatEstimates
end HolomorphicAnosov

