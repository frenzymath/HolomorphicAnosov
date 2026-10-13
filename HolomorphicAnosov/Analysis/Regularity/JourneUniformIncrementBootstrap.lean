import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open scoped BigOperators
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation

/-- A uniformly contracting finite-history recurrence has a uniform bound. (Journé, 1988) -/
theorem uniform_increment_bootstrap
    {A : Type*} (u : A → ℕ → ℝ) (k : A → ℕ → ℕ → ℝ)
    {b q : ℝ} (hb : 0 ≤ b) (hq : q < 1)
    (hk : ∀ a m j, j < m → 0 ≤ k a m j)
    (hrow : ∀ a m, ∑ j ∈ Finset.range m, k a m j ≤ q)
    (hstep : ∀ a m, u a m ≤ b + ∑ j ∈ Finset.range m, k a m j * u a j) :
    ∀ a m, u a m ≤ b / (1 - q) := by
  intro a m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    have hden : 0 < 1 - q := sub_pos.mpr hq
    have hbound : 0 ≤ b / (1 - q) := div_nonneg hb hden.le
    calc
      u a m ≤ b + ∑ j ∈ Finset.range m, k a m j * u a j := hstep a m
      _ ≤ b + ∑ j ∈ Finset.range m, k a m j * (b / (1 - q)) := by
        apply add_le_add le_rfl
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (ih j (Finset.mem_range.mp hj))
          (hk a m j (Finset.mem_range.mp hj))
      _ = b + (∑ j ∈ Finset.range m, k a m j) * (b / (1 - q)) := by
        rw [Finset.sum_mul]
      _ ≤ b + q * (b / (1 - q)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right (hrow a m) hbound)
      _ = b / (1 - q) := by
        field_simp [ne_of_gt hden]
        ring

end HolomorphicAnosov.JourneLeafPolynomialApproximation
