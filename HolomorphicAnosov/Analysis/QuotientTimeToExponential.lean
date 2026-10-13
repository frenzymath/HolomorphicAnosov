import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section
namespace HolomorphicAnosov

/-- A quotient-time geometric bound gives an ordinary exponential bound. -/
theorem quotient_time_to_exponential (k : ℕ) (hk : 0 < k)
    (theta R : ℝ) (htheta : 0 < theta) (htheta1 : theta < 1) (hR : 0 < R) :
    ∃ C lam : ℝ, 0 < C ∧ 0 < lam ∧ lam < 1 ∧
      ∀ n : ℕ, R * theta ^ (n / k) ≤ C * lam ^ n := by
  let lam : ℝ := theta ^ ((k : ℝ)⁻¹)
  have hlam : 0 < lam := Real.rpow_pos_of_pos htheta _
  have hlam1 : lam < 1 := Real.rpow_lt_one htheta.le htheta1 (by positivity)
  have hroot : lam ^ k = theta := Real.rpow_inv_natCast_pow htheta.le (Nat.ne_of_gt hk)
  refine ⟨R / lam ^ k, lam, div_pos hR (pow_pos hlam _), hlam, hlam1, ?_⟩
  intro n
  have hmod : lam ^ k ≤ lam ^ (n % k) :=
    pow_le_pow_of_le_one hlam.le hlam1.le (Nat.le_of_lt (Nat.mod_lt n hk))
  have heq : lam ^ n = theta ^ (n / k) * lam ^ (n % k) := by
    conv_lhs => rw [← Nat.div_add_mod n k]
    rw [pow_add, pow_mul, hroot]
  rw [heq]
  have hthetaq : 0 ≤ theta ^ (n / k) := pow_nonneg htheta.le _
  calc
    R * theta ^ (n / k) = (R / lam ^ k) * (theta ^ (n / k) * lam ^ k) := by
      field_simp
    _ ≤ (R / lam ^ k) * (theta ^ (n / k) * lam ^ (n % k)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmod hthetaq)
        (div_pos hR (pow_pos hlam _)).le

end HolomorphicAnosov
