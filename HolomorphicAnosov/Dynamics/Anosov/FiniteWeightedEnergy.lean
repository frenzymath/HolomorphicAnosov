import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Finite weighted orbit energies

The scalar calculation in GL1 of `g9.hps_anosov_global_lamination` turns a bound at
one finite iterate into a one-step bound for a finite weighted energy. In the geometric
application `a` is the square of the desired contraction factor and `u j` is the squared
norm after `j` iterates. This module asserts no bundle metric or plaque construction.
-/

open scoped BigOperators

namespace HolomorphicAnosov

/-- The shifted finite weighted energy differs by exactly its two endpoint terms.
Agent-written algebra for the finite-sum adaptation in HPS (2.8), pp.13--14.
Proof: induction on the number of terms; the last shifted weight cancels one factor of `a`.
No positivity is needed for this identity, and the empty sum is included. -/
theorem finiteWeightedEnergy_shift (a : ℝ) (ha : a ≠ 0) (u : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range N, (a⁻¹) ^ j * u (j + 1)) =
      a * ((∑ j ∈ Finset.range N, (a⁻¹) ^ j * u j) - u 0 + (a⁻¹) ^ N * u N) := by
  have hweight (n : ℕ) : a * (a⁻¹) ^ (n + 1) = (a⁻¹) ^ n := by
    rw [pow_succ, ← mul_assoc, mul_comm a, mul_assoc, mul_inv_cancel₀ ha, mul_one]
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Finset.sum_range_succ]
    rw [ih]
    calc
      _ = a * ((∑ j ∈ Finset.range N, (a⁻¹) ^ j * u j) +
          (a⁻¹) ^ N * u N - u 0) + (a⁻¹) ^ N * u (N + 1) := by ring
      _ = _ := by rw [← hweight N]; ring

/-- A finite-iterate energy bound gives a one-step bound in the finite weighted energy.
Agent-written scalar part of GL1, following the finite-sum adaptation in HPS (2.8), pp.13--14.
Proof: multiply the endpoint bound by the positive inverse weight, cancel the two powers,
and use the shift identity. The sequence need not be nonnegative for this implication. -/
theorem finiteWeightedEnergy_contract (a : ℝ) (ha : 0 < a) (u : ℕ → ℝ) (N : ℕ)
    (hN : u N ≤ a ^ N * u 0) :
    (∑ j ∈ Finset.range N, (a⁻¹) ^ j * u (j + 1)) ≤
      a * (∑ j ∈ Finset.range N, (a⁻¹) ^ j * u j) := by
  have hlast : (a⁻¹) ^ N * u N ≤ u 0 := by
    calc
      (a⁻¹) ^ N * u N ≤ (a⁻¹) ^ N * (a ^ N * u 0) :=
        mul_le_mul_of_nonneg_left hN (pow_nonneg (inv_nonneg.mpr ha.le) N)
      _ = u 0 := by rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ ha.ne', one_pow, one_mul]
  rw [finiteWeightedEnergy_shift a ha.ne' u N]
  exact mul_le_mul_of_nonneg_left (by linarith) ha.le


end HolomorphicAnosov
