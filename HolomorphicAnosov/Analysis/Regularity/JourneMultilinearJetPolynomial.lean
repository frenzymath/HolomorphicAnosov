import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic

/-!
This file develops finite coordinate realizations of multilinear jets.
-/ 

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation

/-- Any finite family of multilinear forms determines a translated coordinate polynomial of the expected total degree. -/
theorem multilinear_jet_polynomial_exists {N n : ℕ}
    (a : EuclideanSpace ℝ (Fin N))
    (T : (j : Fin (n + 1)) → ContinuousMultilinearMap ℝ
      (fun _ : Fin j.val ↦ EuclideanSpace ℝ (Fin N)) ℝ) :
    ∃ P : MvPolynomial (Fin N) ℝ, P.totalDegree ≤ n ∧
      ∀ y : EuclideanSpace ℝ (Fin N),
        MvPolynomial.eval (fun i ↦ y i) P =
          ∑ j : Fin (n + 1), (j.val.factorial : ℝ)⁻¹ * T j (fun _ ↦ y - a) := by
  classical
  let b := EuclideanSpace.basisFun (Fin N) ℝ
  let Q (j : Fin (n + 1)) : MvPolynomial (Fin N) ℝ :=
    ∑ r : Fin j.val → Fin N,
      MvPolynomial.C ((j.val.factorial : ℝ)⁻¹ * T j (fun i ↦ b (r i))) *
        ∏ i : Fin j.val, (MvPolynomial.X (r i) - MvPolynomial.C (a (r i)))
  refine ⟨∑ j, Q j, ?_, ?_⟩
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro j _
    apply le_trans ?_ (Nat.le_of_lt_succ j.isLt)
    apply MvPolynomial.totalDegree_finsetSum_le
    intro r _
    apply (MvPolynomial.totalDegree_mul _ _).trans
    rw [MvPolynomial.totalDegree_C, zero_add]
    apply (MvPolynomial.totalDegree_finsetProd _ _).trans
    calc
      _ ≤ ∑ _i : Fin j.val, 1 := by
        apply Finset.sum_le_sum
        intro i _
        exact (MvPolynomial.totalDegree_sub_C_le _ _).trans (by simp)
      _ = j.val := by simp
  · intro y
    have heval : MvPolynomial.eval (fun i ↦ y i) (∑ j, Q j) =
        ∑ j : Fin (n + 1), (j.val.factorial : ℝ)⁻¹ * T j (fun _ ↦ y - a) := by
      rw [MvPolynomial.eval_sum]
      apply Finset.sum_congr rfl
      intro j _
      have hsum : y - a = ∑ k : Fin N, (y k - a k) • b k := by
        simpa [b, EuclideanSpace.basisFun_repr] using (b.sum_repr (y - a)).symm
      have hexpand := (T j).toMultilinearMap.map_sum
        (fun (_i : Fin j.val) (k : Fin N) ↦ (y k - a k) • b k)
      change (T j) (fun _ ↦ ∑ k : Fin N, (y k - a k) • b k) =
        ∑ r : Fin j.val → Fin N,
          (T j) (fun i ↦ (y (r i) - a (r i)) • b (r i)) at hexpand
      rw [hsum, hexpand, Finset.mul_sum]
      simp only [Q, MvPolynomial.eval_sum, map_mul, map_prod, map_sub,
        MvPolynomial.eval_C, MvPolynomial.eval_X]
      apply Finset.sum_congr rfl
      intro r _
      rw [(T j).map_smul_univ]
      simp only [smul_eq_mul]
      ring
    exact heval

end HolomorphicAnosov.JourneLeafPolynomialApproximation
