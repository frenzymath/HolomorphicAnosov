import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Mather's finite-energy contraction calculation

Source: Hirsch–Pugh, Stable Manifolds and Hyperbolic Sets (1969), Theorem 3.1,
printed p.148, the displayed finite-sum estimate. The scalar calculation applies
both to forward stable norms and to backward unstable norms of the original map.
-/

namespace HolomorphicAnosov.FactOneFiniteEnergy

/-- Finite squared energies contract under a shifted exponentially bounded nonnegative
sequence. Source: Hirsch–Pugh (1969), Theorem 3.1, p.148.

Proof: each term b(j)^2 is at most C^2 b(0)^2, so the q-term sum S is at most
q C^2 b(0)^2. The terminal term is at most (C r^q)^2 b(0)^2. Write
δ=1-(C r^q)^2≥0. Then S-b(0)^2+b(q)^2≤S-δ b(0)^2≤(1-δ/(q C^2))S.
The positive denominator is justified by q>0 and C≥1. Zero sequences, q=1,
and C=1 are included; r=0 is permitted for this non-strict inequality. -/
theorem scalar_energy_contraction
    (C r : ℝ) (hC : 1 ≤ C) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (q : ℕ) (hq : 0 < q) (hsmall : C * r ^ q < 1)
    (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n)
    (hbound : ∀ n, b n ≤ C * r ^ n * b 0) :
    (∑ j ∈ Finset.range q, b j ^ 2) - b 0 ^ 2 + b q ^ 2 ≤
      (1 - (1 - (C * r ^ q) ^ 2) / ((q : ℝ) * C ^ 2)) *
        (∑ j ∈ Finset.range q, b j ^ 2) := by
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hden : 0 < (q : ℝ) * C ^ 2 := mul_pos (by exact_mod_cast hq) (by positivity)
  have hδ : 0 ≤ 1 - (C * r ^ q) ^ 2 := by
    have hpos : 0 ≤ C * r ^ q := mul_nonneg hC0 (pow_nonneg hr q)
    nlinarith
  have hend : b q ^ 2 ≤ (C * r ^ q) ^ 2 * b 0 ^ 2 := by
    have ht := hbound q
    have hp : 0 ≤ C * r ^ q * b 0 := mul_nonneg (mul_nonneg hC0 (pow_nonneg hr q)) (hb 0)
    simpa only [mul_pow] using (sq_le_sq₀ (hb q) hp).2 ht
  have hsum : (∑ j ∈ Finset.range q, b j ^ 2) ≤ (q : ℝ) * C ^ 2 * b 0 ^ 2 := by
    calc
      _ ≤ ∑ _j ∈ Finset.range q, C ^ 2 * b 0 ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        have ht := (hbound j).trans (mul_le_mul_of_nonneg_right
          (mul_le_of_le_one_right hC0 (pow_le_one₀ hr hr1)) (hb 0))
        have hp : 0 ≤ C * b 0 := mul_nonneg hC0 (hb 0)
        nlinarith [hb j]
      _ = _ := by simp; ring
  have hratio : (1 - (C * r ^ q) ^ 2) / ((q : ℝ) * C ^ 2) *
      (∑ j ∈ Finset.range q, b j ^ 2) ≤ (1 - (C * r ^ q) ^ 2) * b 0 ^ 2 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).2
    nlinarith [mul_le_mul_of_nonneg_left hsum hδ]
  nlinarith


/-- The source coefficient lies strictly between zero and one.
Source: Hirsch–Pugh (1969), Theorem 3.1, p.148. Since 0<C r^q<1, the numerator
δ lies in (0,1), while q C²≥1. Thus 0<δ/(q C²)<1. This includes q=1 and C=1. -/
theorem contraction_coefficient_bounds
    (C r : ℝ) (hC : 1 ≤ C) (hr : 0 < r)
    (q : ℕ) (hq : 0 < q) (hsmall : C * r ^ q < 1) :
    0 < 1 - (1 - (C * r ^ q) ^ 2) / ((q : ℝ) * C ^ 2) ∧
      1 - (1 - (C * r ^ q) ^ 2) / ((q : ℝ) * C ^ 2) < 1 := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hden1 : 1 ≤ (q : ℝ) * C ^ 2 := by nlinarith [sq_nonneg (C - 1)]
  have hden : 0 < (q : ℝ) * C ^ 2 := lt_of_lt_of_le zero_lt_one hden1
  have hp : 0 < C * r ^ q := mul_pos hCpos (pow_pos hr q)
  have hδ : 0 < 1 - (C * r ^ q) ^ 2 := by nlinarith
  have hδlt : 1 - (C * r ^ q) ^ 2 < (q : ℝ) * C ^ 2 := by nlinarith
  constructor
  · have := (div_lt_one hden).mpr hδlt
    linarith
  · have := div_pos hδ hden
    linarith


end HolomorphicAnosov.FactOneFiniteEnergy

