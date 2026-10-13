import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Small geometric tails after passing to a positive iterate

Source: Bowen, *Markov Partitions for Axiom A Diffeomorphisms* (1970),
p.732, the choice of the iterate immediately before Lemma 14.
-/

namespace HolomorphicAnosov

/-- A nonnegative contraction rate admits a positive iterate whose geometric tail
is below any prescribed positive tolerance.

Source: Bowen (1970), p.732, choice of the iterate before Lemma 14. Powers of the
rate tend to zero, so choose a positive exponent whose power is below both one
half and half the tolerance. The geometric-series formula bounds its tail by
twice that power. Rate zero is included. -/
theorem exists_pos_iterate_geometric_tail_lt {rate tolerance : ℝ}
    (h0 : 0 ≤ rate) (h1 : rate < 1) (ht : 0 < tolerance) :
    ∃ m : ℕ, 0 < m ∧ (∑' k : ℕ, (rate ^ m) ^ (k + 1)) < tolerance := by
  have hsmall := (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).eventually
    (gt_mem_nhds (show (0 : ℝ) < min (1 / 2) (tolerance / 2) from
      lt_min (by norm_num) (half_pos ht)))
  obtain ⟨m, hm, hpow⟩ := ((Filter.eventually_gt_atTop 0).and hsmall).exists
  have hhalf : rate ^ m < 1 / 2 := (lt_min_iff.mp hpow).1
  have htiny : rate ^ m < tolerance / 2 := (lt_min_iff.mp hpow).2
  have hp0 : 0 ≤ rate ^ m := pow_nonneg h0 _
  have hp1 : rate ^ m < 1 := lt_trans hhalf (by norm_num)
  have hsum : (∑' k : ℕ, (rate ^ m) ^ (k + 1)) =
      rate ^ m / (1 - rate ^ m) := by
    simpa only [pow_succ, div_eq_mul_inv, mul_comm] using
      ((hasSum_geometric_of_lt_one hp0 hp1).mul_left (rate ^ m)).tsum_eq
  refine ⟨m, hm, ?_⟩
  rw [hsum, div_lt_iff₀ (sub_pos.mpr hp1)]
  nlinarith [mul_pos ht (show (0 : ℝ) < 1 / 2 - rate ^ m by linarith)]

end HolomorphicAnosov

