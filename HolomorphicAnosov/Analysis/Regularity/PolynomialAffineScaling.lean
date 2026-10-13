import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

open MvPolynomial
noncomputable section
namespace HolomorphicAnosov

/-- Affine substitution preserves total degree and scales each translated coefficient. -/
theorem polynomial_affine_scaling {N : ℕ} (P : MvPolynomial (Fin N) ℝ) (a : EuclideanSpace ℝ (Fin N))
    (r : ℝ) :
    ∃ Q : MvPolynomial (Fin N) ℝ, Q.totalDegree ≤ P.totalDegree ∧
      (∀ x : EuclideanSpace ℝ (Fin N), eval (fun i ↦ x i) Q =
        eval (fun i ↦ (a + r • x) i) P) ∧
      ∀ β, Q.coeff β = r ^ (β.sum fun _ k ↦ k) *
        (eval₂Hom C (fun i ↦ C (a i) + X i) P).coeff β := by
  let T := eval₂Hom (C : ℝ →+* MvPolynomial (Fin N) ℝ) (fun i ↦ C (a i) + X i) P
  let Q := eval₂Hom (C : ℝ →+* MvPolynomial (Fin N) ℝ) (fun i ↦ C r * X i) T
  refine ⟨Q, ?_, ?_, ?_⟩
  · classical
    have hQ : Q = eval₂Hom C (fun i ↦ C (a i) + C r * X i) P := by
      have hh : (eval₂Hom C (fun i ↦ C r * X i)).comp
          (eval₂Hom C (fun i ↦ C (a i) + X i)) =
          eval₂Hom C (fun i ↦ C (a i) + C r * X i) := by
        ext <;> simp
      exact RingHom.congr_fun hh P
    rw [hQ]
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    apply totalDegree_finsetSum_le
    intro d hd
    rw [eval₂Hom_monomial]
    refine (totalDegree_mul _ _).trans ?_
    simp only [totalDegree_C, zero_add, Finsupp.prod]
    refine (totalDegree_finsetProd _ _).trans ?_
    apply le_trans (Finset.sum_le_sum fun i hi ↦ ?_) (le_totalDegree hd)
    calc
      ((C (a i) + C r * X i : MvPolynomial (Fin N) ℝ) ^ d i).totalDegree
          ≤ d i * (C (a i) + C r * X i : MvPolynomial (Fin N) ℝ).totalDegree :=
        totalDegree_pow _ _
      _ ≤ d i * 1 := Nat.mul_le_mul_left _ <| (totalDegree_add _ _).trans <|
        max_le (by simp) <| (totalDegree_mul _ _).trans (by simp)
      _ = d i := Nat.mul_one _
  · intro x
    change eval (fun i ↦ x i) (eval₂ C (fun i ↦ C r * X i)
      (eval₂ C (fun i ↦ C (a i) + X i) P)) = _
    simp only [eval_eval₂, map_mul, eval_C, eval_X]
    have hc : (eval (fun i ↦ x i)).comp C = RingHom.id ℝ := by ext z; simp
    rw [hc, eval₂_id]
    simp only [eval_eval₂, map_add, eval_C, eval_X]
    congr 1
    · ext z
      simp
  · intro β
    change (eval₂Hom C (fun i ↦ C r * X i) T).coeff β = _
    change _ = r ^ (β.sum fun _ k ↦ k) * T.coeff β
    induction T using MvPolynomial.induction_on' with
    | add p q hp hq =>
      simpa only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, mul_add] using congrArg₂ (· + ·) hp hq
    | monomial d c =>
      rw [eval₂Hom_monomial]
      have hm : d.prod (fun i k ↦ (C r * X i : MvPolynomial (Fin N) ℝ) ^ k) =
          C (r ^ (d.sum fun _ k ↦ k)) * monomial d 1 := by
        simp only [Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib]
        rw [prod_X_pow_eq_monomial]
        congr 1
        simp only [← map_pow, ← map_prod, ← Finset.prod_pow_eq_pow_sum]
      rw [hm, ← mul_assoc, ← map_mul, C_mul_monomial, coeff_monomial, coeff_monomial]
      by_cases h : d = β
      · subst β
        simp [mul_comm]
      · simp [h]
end HolomorphicAnosov
