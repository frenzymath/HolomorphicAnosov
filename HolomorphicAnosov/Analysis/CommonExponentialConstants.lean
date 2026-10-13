import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section
namespace HolomorphicAnosov

/-- Two positive exponential estimates with rates below one share larger constants and rate. -/
theorem common_exponential_constants (C1 C2 lam1 lam2 : ℝ)
    (hC1 : 0 < C1) (hC2 : 0 < C2) (hlam1 : 0 < lam1) (hlam2 : 0 < lam2)
    (hlam1_lt : lam1 < 1) (hlam2_lt : lam2 < 1) :
    ∃ C lam : ℝ, 0 < C ∧ 0 < lam ∧ lam < 1 ∧
      (∀ n : ℕ, C1 * lam1 ^ n ≤ C * lam ^ n) ∧
      (∀ n : ℕ, C2 * lam2 ^ n ≤ C * lam ^ n) := by
  refine ⟨max C1 C2, max lam1 lam2, lt_of_lt_of_le hC1 (le_max_left _ _),
    lt_of_lt_of_le hlam1 (le_max_left _ _), max_lt hlam1_lt hlam2_lt, ?_, ?_⟩
  · intro n
    exact mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ hlam1.le (le_max_left _ _) n)
      (pow_nonneg hlam1.le n) (hC1.le.trans (le_max_left _ _))
  · intro n
    exact mul_le_mul (le_max_right _ _) (pow_le_pow_left₀ hlam2.le (le_max_right _ _) n)
      (pow_nonneg hlam2.le n) (hC2.le.trans (le_max_right _ _))

end HolomorphicAnosov
