import HolomorphicAnosov.Linear.HyperbolicDecayAux06

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov

/-- If the spectral radius of an element of a Banach algebra is less than one, its powers converge to zero in norm. (Alves, Proposition 3.2) -/
theorem powers_tendsto_zero_of_spectralRadius_lt_one
    {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]
    (b : B) (hr : spectralRadius ℂ b < 1) :
    Tendsto (fun n : ℕ ↦ b ^ n) atTop (𝓝 0) := by
  have hrfin : spectralRadius ℂ b ≠ ⊤ := ne_top_of_lt (hr.trans ENNReal.one_lt_top)
  have hrreal : (spectralRadius ℂ b).toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hrfin ENNReal.one_ne_top).2 hr
  obtain ⟨ρ, hrρ, hρone⟩ := exists_between hrreal
  have hρpos : 0 < ρ := lt_of_le_of_lt ENNReal.toReal_nonneg hrρ
  have hroot : Tendsto (fun n : ℕ ↦ ‖b ^ n‖ ^ (1 / (n : ℝ))) atTop
      (𝓝 (spectralRadius ℂ b).toReal) := by
    have h := (ENNReal.tendsto_toReal hrfin).comp
      (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius b)
    simpa only [Function.comp_def, ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)]
      using h
  have hbnd : ∀ᶠ n : ℕ in atTop, ‖b ^ n‖ ≤ ρ ^ n := by
    filter_upwards [hroot.eventually_lt_const hrρ, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
    have := Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _)
      hn.le (le_of_lt hnreal)
    simpa only [← Real.rpow_mul (norm_nonneg _), one_div, inv_mul_cancel₀ hnreal.ne',
      Real.rpow_one, Real.rpow_natCast] using this
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (Filter.Eventually.of_forall fun n ↦ norm_nonneg (b ^ n)) hbnd
      (tendsto_pow_atTop_nhds_zero_of_lt_one hρpos.le hρone))



end HolomorphicAnosov
