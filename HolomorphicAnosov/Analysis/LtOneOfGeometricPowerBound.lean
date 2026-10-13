import Mathlib.Analysis.SpecificLimits.Basic

namespace HolomorphicAnosov
open scoped _root_.Topology

/-- A real number whose powers admit a fixed multiple of a decaying geometric
bound is strictly below one. This numerical step expands the multiplier argument
in Zhang, Lemma 4.2, printed p.14. The proof is an agent-written specialization of
Mathlib's geometric convergence: if the number were at least one, all its powers
would be at least one, while the upper bound is eventually below one. No sign
assumption on the fixed multiple or on the bounded number is needed. -/
theorem lt_one_of_geometric_power_bound (x C rate : ℝ)
    (hrate : 0 ≤ rate) (hrate1 : rate < 1)
    (hbound : ∀ n : ℕ, x ^ n ≤ C * rate ^ n) : x < 1 := by
  have ht : Filter.Tendsto (fun n : ℕ ↦ C * rate ^ n) Filter.atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hrate hrate1).const_mul C
  obtain ⟨n, hn⟩ := Filter.Eventually.exists (ht.eventually_lt_const zero_lt_one)
  by_contra h
  have hp : 1 ≤ x ^ n := one_le_pow₀ (le_of_not_gt h)
  exact (not_lt_of_ge (hp.trans (hbound n))) hn

end HolomorphicAnosov
