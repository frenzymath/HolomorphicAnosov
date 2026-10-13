import HolomorphicAnosov.Linear.HyperbolicRealSplitting.PowApplyNormLe
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace HolomorphicAnosov

/-- If a positive power of a continuous real-linear operator has norm less than one half, all its
powers satisfy an exponential decay bound with constants `C ≥ 1` and `0 < r < 1`. (Alves, Thm
2.7 and Prop. 3.2, Eq. (15)) -/
theorem exponential_of_contracting_power
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : V →L[ℝ] V) (k : ℕ) (hk : 0 < k) (hsmall : ‖T ^ k‖ < 1 / 2) :
    ∃ C r : ℝ, 1 ≤ C ∧ 0 < r ∧ r < 1 ∧
      ∀ n v, ‖(T ^ n) v‖ ≤ C * r ^ n * ‖v‖ := by
  have hblock : ∀ v, ‖(T ^ k) v‖ ≤ (1 / 2 : ℝ) * ‖v‖ := fun v ↦
    (T ^ k).le_opNorm v |>.trans
      (mul_le_mul_of_nonneg_right hsmall.le (norm_nonneg v))
  let R := (max 1 ‖T‖) ^ k
  have hR : 0 < R := pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  have hresidue : ∀ j, j < k → ∀ v, ‖(T ^ j) v‖ ≤ R * ‖v‖ := by
    intro j hj v
    refine (pow_apply_norm_le T j v).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg v))
    exact (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) hj.le)
  have hblocks : ∀ q v, ‖(T ^ (k * q)) v‖ ≤ (1 / 2 : ℝ) ^ q * ‖v‖ := by
    intro q
    induction q with
    | zero => intro v; simp
    | succ q ih =>
      intro v
      rw [Nat.mul_succ, pow_add]
      change ‖(T ^ (k * q)) ((T ^ k) v)‖ ≤ _
      exact (ih _).trans (by
        simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
          mul_le_mul_of_nonneg_left (hblock v) (pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) q))
  have hquot : ∀ n v, ‖(T ^ n) v‖ ≤ R * (1 / 2 : ℝ) ^ (n / k) * ‖v‖ := by
    intro n v
    conv_lhs => rw [← Nat.div_add_mod n k]
    rw [pow_add]
    change ‖(T ^ (k * (n / k))) ((T ^ (n % k)) v)‖ ≤ _
    exact (hblocks _ _).trans (by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_left (hresidue _ (Nat.mod_lt n hk) v)
          (pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) (n / k)))
  let r : ℝ := (1 / 2 : ℝ) ^ ((k : ℝ)⁻¹)
  have hr : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by positivity)
  have hroot : r ^ k = (1 / 2 : ℝ) :=
    Real.rpow_inv_natCast_pow (by norm_num) (Nat.ne_of_gt hk)
  let C := max 1 (R / r ^ k)
  refine ⟨C, r, le_max_left _ _, hr, hr1, fun n v ↦ (hquot n v).trans ?_⟩
  have hmod : r ^ k ≤ r ^ (n % k) :=
    pow_le_pow_of_le_one hr.le hr1.le (Nat.le_of_lt (Nat.mod_lt n hk))
  have heq : r ^ n = (1 / 2 : ℝ) ^ (n / k) * r ^ (n % k) := by
    conv_lhs => rw [← Nat.div_add_mod n k]
    rw [pow_add, pow_mul, hroot]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
  calc
    R * (1 / 2 : ℝ) ^ (n / k) =
        (R / r ^ k) * ((1 / 2 : ℝ) ^ (n / k) * r ^ k) := by field_simp
    _ ≤ (R / r ^ k) * ((1 / 2 : ℝ) ^ (n / k) * r ^ (n % k)) := by gcongr
    _ ≤ C * ((1 / 2 : ℝ) ^ (n / k) * r ^ (n % k)) := by
      apply mul_le_mul_of_nonneg_right (le_max_right _ _); positivity
    _ = C * r ^ n := by rw [heq]

end HolomorphicAnosov
