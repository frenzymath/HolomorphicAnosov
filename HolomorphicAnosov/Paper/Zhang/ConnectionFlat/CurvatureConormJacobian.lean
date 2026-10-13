import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

noncomputable section
namespace HolomorphicAnosov
namespace ConnectionFlatEstimates

/-- The curvature bound and determinant–conorm inequality imply `R ≤ C * J / μ ^ (2 * k)` when `μ >
0` and `J = q ^ 2 * D ^ 2`. (Zhang, eq. (10)) -/
theorem curvature_le_conorm_jacobian {R C q u D μ J : ℝ} (k : ℕ)
    (hC : 0 ≤ C) (hu : 0 ≤ u) (hμ : 0 < μ)
    (hcurvature : R ≤ C * q ^ 2 * u ^ 2)
    (hdet : u * μ ^ k ≤ D) (hJ : J = q ^ 2 * D ^ 2) :
    R ≤ C * J / μ ^ (2 * k) := by
  have hsq : (u * μ ^ k) ^ 2 ≤ D ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hu (pow_nonneg hμ.le _)) hdet 2
  apply (le_div_iff₀ (pow_pos hμ _)).mpr
  calc
    R * μ ^ (2 * k) ≤ (C * q ^ 2 * u ^ 2) * μ ^ (2 * k) :=
      mul_le_mul_of_nonneg_right hcurvature (pow_nonneg hμ.le _)
    _ = C * q ^ 2 * (u * μ ^ k) ^ 2 := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm k 2]
      ring
    _ ≤ C * q ^ 2 * D ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (mul_nonneg hC (sq_nonneg q))
    _ = C * J := by rw [hJ]; ring

end ConnectionFlatEstimates
end HolomorphicAnosov
