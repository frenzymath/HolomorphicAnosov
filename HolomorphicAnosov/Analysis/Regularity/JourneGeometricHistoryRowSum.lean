import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic

open scoped BigOperators
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation

/-- A backward geometric history and a forward geometric history have uniformly
bounded row sums.

This agent-written scalar estimate supplies the row bound in the J8 induction
of the parent Journé approximation proof, corresponding to the geometric sums
on printed p.191 of Journé (1988). The actual kernel domination is a hypothesis;
the theorem does not construct the interpolation coefficients. Sum the assumed
domination, distribute the two sums, and reflect the backward indices to obtain
the powers with exponents 1 through m. The two finite geometric sums are bounded
by r/(1-r) and 1/(1-s). Multiplication by the nonnegative amplitudes preserves
these bounds. Time zero, zero ratios and zero amplitudes are included. -/
theorem geometric_history_row_sum_le
    (k : ℕ → ℕ → ℝ) {A B r s : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hk : ∀ m j, j < m → k m j ≤ A * r ^ (m - j) + B * s ^ j)
    (m : ℕ) :
    ∑ j ∈ Finset.range m, k m j ≤ A * (r / (1 - r)) + B * (1 / (1 - s)) := by
  have hback : ∑ j ∈ Finset.range m, r ^ (m - j) ≤ r / (1 - r) := by
    have hreflect := Finset.sum_Ico_reflect (fun j => r ^ j) 0
      (m := m) (n := m) (Nat.le_succ m)
    have heq : ∑ j ∈ Finset.range m, r ^ (m - j) =
        ∑ j ∈ Finset.Ico 1 (m + 1), r ^ j := by
      simpa using hreflect
    rw [heq]
    simpa using (geom_sum_Ico_le_of_lt_one (m := 1) (n := m + 1) hr0 hr1)
  have hforward : ∑ j ∈ Finset.range m, s ^ j ≤ 1 / (1 - s) := by
    simpa using (geom_sum_Ico_le_of_lt_one (m := 0) (n := m) hs0 hs1)
  calc
    ∑ j ∈ Finset.range m, k m j ≤
        ∑ j ∈ Finset.range m, (A * r ^ (m - j) + B * s ^ j) :=
      Finset.sum_le_sum fun j hj => hk m j (Finset.mem_range.mp hj)
    _ = A * (∑ j ∈ Finset.range m, r ^ (m - j)) +
        B * (∑ j ∈ Finset.range m, s ^ j) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ A * (r / (1 - r)) + B * (1 / (1 - s)) :=
      add_le_add (mul_le_mul_of_nonneg_left hback hA)
        (mul_le_mul_of_nonneg_left hforward hB)

end HolomorphicAnosov.JourneLeafPolynomialApproximation
