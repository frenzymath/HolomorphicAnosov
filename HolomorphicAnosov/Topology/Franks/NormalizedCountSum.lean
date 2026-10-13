import Mathlib.Analysis.SpecificLimits.Basic

open Filter
open scoped Topology _root_.Topology BigOperators

namespace HolomorphicAnosov

/-- Manning (1974), Theorem A, Case 2, p.426: summing finitely many basic-set
counts whose own exponential normalizations tend to one gives, after normalization
by a common maximal rate, the number of pieces attaining that rate.

For a smaller rate, factor its normalized count as its own normalization times
the geometric sequence of rate ratios; this tends to zero. For an equal rate the
limit is one. Pass the limit through the finite sum. The empty family is allowed,
and the common upper rate need not be attained for this first conclusion. -/
theorem franks_manning_normalized_count_sum
    {ι : Type*} (s : Finset ι) (N : ι → ℕ → ℝ) (r : ι → ℝ) (R : ℝ)
    (hR : 0 < R) (hr : ∀ i ∈ s, 0 < r i) (hle : ∀ i ∈ s, r i ≤ R)
    (hN : ∀ i ∈ s, Tendsto (fun m ↦ N i m / r i ^ m) atTop (𝓝 1)) :
    Tendsto (fun m ↦ (∑ i ∈ s, N i m) / R ^ m) atTop
      (𝓝 ((s.filter (fun i ↦ r i = R)).card : ℝ)) := by
  classical
  have hi (i : ι) (his : i ∈ s) :
      Tendsto (fun m ↦ N i m / R ^ m) atTop (𝓝 (if r i = R then 1 else 0)) := by
    by_cases he : r i = R
    · simpa only [he, ite_true] using hN i his
    · have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
        (div_nonneg (hr i his).le hR.le) ((div_lt_one hR).mpr (lt_of_le_of_ne (hle i his) he))
      have ht := (hN i his).mul hpow
      simpa only [mul_zero, ite_eq_right he, div_pow,
        div_mul_div_cancel₀ (pow_ne_zero _ (ne_of_gt (hr i his)))] using ht
  convert tendsto_finsetSum s hi using 1 <;> simp [div_eq_mul_inv, Finset.sum_mul]

/-- When the upper rate is attained, Manning's normalized limit is a positive
integer. Consequently the total count is positive for all sufficiently large
periods. This is the eventual-positivity input in Step 11(C5), excluding a root
of unity through the determinant fixed-point formula. It does not supply that
formula or the individual basic-set count asymptotics. -/
theorem franks_manning_count_sum_eventually_pos
    {ι : Type*} (s : Finset ι) (N : ι → ℕ → ℝ) (r : ι → ℝ) (R : ℝ)
    (hR : 0 < R) (hr : ∀ i ∈ s, 0 < r i) (hle : ∀ i ∈ s, r i ≤ R)
    (hN : ∀ i ∈ s, Tendsto (fun m ↦ N i m / r i ^ m) atTop (𝓝 1))
    (hmax : ∃ i ∈ s, r i = R) :
    ∀ᶠ m in atTop, 0 < ∑ i ∈ s, N i m := by
  classical
  have hcard : (0 : ℝ) < (s.filter (fun i ↦ r i = R)).card := by
    exact_mod_cast Finset.card_pos.mpr (by simpa only [Finset.filter_nonempty_iff] using hmax)
  have ht := franks_manning_normalized_count_sum s N r R hR hr hle hN
  filter_upwards [ht.eventually_const_lt hcard] with m hm
  exact (div_pos_iff_of_pos_right (pow_pos hR m)).mp hm

end HolomorphicAnosov

