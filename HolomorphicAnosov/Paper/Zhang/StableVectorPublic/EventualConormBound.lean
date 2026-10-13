import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
namespace HolomorphicAnosov

open Filter in
/-- A uniform exponential lower bound for the conorm implies that the conorm is at least one in
every fibre for all sufficiently large iterates. (Zhang, (29)) -/
theorem eventually_conorm_ge_one {X : Type*}
    (m : ℕ → X → ℝ) (A lam : ℝ) (hA : 0 < A) (hlam : 1 < lam)
    (hm : ∀ n x, A⁻¹ * lam ^ n ≤ m n x) :
    ∀ᶠ n in atTop, ∀ x, 1 ≤ m n x := by
  have hpow : ∀ᶠ n : ℕ in atTop, A ≤ lam ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt hlam).eventually_ge_atTop A
  filter_upwards [hpow] with n hn x
  calc
    1 = A⁻¹ * A := (inv_mul_cancel₀ hA.ne').symm
    _ ≤ A⁻¹ * lam ^ n := mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hA.le)
    _ ≤ m n x := hm n x



end HolomorphicAnosov
