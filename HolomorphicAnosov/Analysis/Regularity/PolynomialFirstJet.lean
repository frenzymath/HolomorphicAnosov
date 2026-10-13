import HolomorphicAnosov.Analysis.Regularity.PolynomialBallDerivativeEstimate
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import HolomorphicAnosov.Analysis.Regularity.PolynomialTranslateCoeffZero

namespace HolomorphicAnosov

open Filter
open scoped Topology _root_.Topology

noncomputable def polynomialFirstJet {N : ℕ} (P : MvPolynomial (Fin N) ℝ)
    (a : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ :=
  ∑ i : Fin N, (polynomialTranslate P a).coeff (Finsupp.single i 1) •
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N ↦ ℝ) i)



lemma polynomialFirstJet_add {N : ℕ} (P Q : MvPolynomial (Fin N) ℝ)
    (a : EuclideanSpace ℝ (Fin N)) :
    polynomialFirstJet (P + Q) a = polynomialFirstJet P a + polynomialFirstJet Q a := by
  simp only [polynomialFirstJet, polynomialTranslate, map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    add_smul, Finset.sum_add_distrib]



lemma polynomialFirstJet_mul_X {N : ℕ} (P : MvPolynomial (Fin N) ℝ)
    (a : EuclideanSpace ℝ (Fin N)) (j : Fin N) :
    polynomialFirstJet (P * MvPolynomial.X j) a =
      (a j) • polynomialFirstJet P a +
        (MvPolynomial.eval (fun i ↦ a i) P) •
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N ↦ ℝ) j) := by
  classical
  have hcoeff : ∀ i : Fin N,
      (polynomialTranslate (P * MvPolynomial.X j) a).coeff (Finsupp.single i 1) =
        a j * (polynomialTranslate P a).coeff (Finsupp.single i 1) +
          if i = j then MvPolynomial.eval (fun i ↦ a i) P else 0 := by
    intro i
    unfold polynomialTranslate
    rw [map_mul, MvPolynomial.eval₂Hom_X', mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    rw [mul_comm _ (MvPolynomial.C (a j)), MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_mul_X']
    by_cases hij : i = j
    · subst i
      simp only [Finsupp.support_single _ (by norm_num : (1 : ℕ) ≠ 0),
        Finset.mem_singleton, ite_true, tsub_self]
      exact congrArg (a j * (polynomialTranslate P a).coeff (Finsupp.single j 1) + ·)
        (polynomialTranslate_coeff_zero P a)
    · simp [hij, Ne.symm hij]
  simp only [polynomialFirstJet, hcoeff, add_smul, Finset.sum_add_distrib,
    mul_smul, ← Finset.smul_sum]
  congr 1
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]



lemma polynomial_hasFDerivAt_firstJet {N : ℕ} (P : MvPolynomial (Fin N) ℝ)
    (a : EuclideanSpace ℝ (Fin N)) :
    HasFDerivAt (fun y : EuclideanSpace ℝ (Fin N) ↦ MvPolynomial.eval (fun i ↦ y i) P)
      (polynomialFirstJet P a) a := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
      have hj : polynomialFirstJet (MvPolynomial.C c) a = 0 := by
        simp [polynomialFirstJet, polynomialTranslate, MvPolynomial.coeff_C,
          eq_comm, Finsupp.single_eq_zero]
      simpa only [hj, MvPolynomial.eval_C] using hasFDerivAt_const c a
  | add P Q hP hQ =>
      convert hP.add hQ using 1
      · funext y
        simp only [map_add, Pi.add_apply]
      · exact polynomialFirstJet_add P Q a
  | mul_X P j hP =>
      convert hP.mul ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N ↦ ℝ) j).hasFDerivAt) using 1
      · funext y
        simp only [map_mul, MvPolynomial.eval_X, Pi.mul_apply, PiLp.proj_apply]
      · rw [polynomialFirstJet_mul_X]
        exact add_comm _ _

-- Algebraic partial differentiation commutes with translation of the same polynomial.


lemma polynomialPartialAt_single {N : ℕ} (P : MvPolynomial (Fin N) ℝ)
    (a : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    polynomialPartialAt P a (Finsupp.single i 1) =
      (polynomialTranslate P a).coeff (Finsupp.single i 1) := by
  simp [polynomialPartialAt, Finsupp.prod_single_index]

-- The Euclidean L2 operator norm is bounded by the finite coefficient sum, not a changed norm.


lemma polynomialFirstJet_norm_bound {N : ℕ} (P : MvPolynomial (Fin N) ℝ)
    (a : EuclideanSpace ℝ (Fin N)) (M : ℝ) (hM : 0 ≤ M)
    (hcoeff : ∀ i : Fin N, |polynomialPartialAt P a (Finsupp.single i 1)| ≤ M) :
    ‖polynomialFirstJet P a‖ ≤ (N : ℝ) * M := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) hM)
  intro v
  change ‖(∑ i : Fin N, (polynomialTranslate P a).coeff (Finsupp.single i 1) •
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N ↦ ℝ) i)) v‖ ≤ (N : ℝ) * M * ‖v‖
  rw [sum_apply]
  calc
    ‖∑ i : Fin N, ((polynomialTranslate P a).coeff (Finsupp.single i 1) •
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N ↦ ℝ) i)) v‖ ≤
        ∑ i : Fin N, ‖((polynomialTranslate P a).coeff (Finsupp.single i 1) •
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N ↦ ℝ) i)) v‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, M * ‖v‖ := by
      apply Finset.sum_le_sum
      intro i _hi
      simpa only [smul_apply, PiLp.proj_apply, norm_smul,
        Real.norm_eq_abs] using
        mul_le_mul (by simpa only [polynomialPartialAt_single] using hcoeff i)
          (PiLp.norm_apply_le v i) (norm_nonneg (v i)) hM
    _ = (N : ℝ) * M * ‖v‖ := by simp [mul_assoc]



lemma polynomialFirstJet_sub {N : ℕ} (P Q : MvPolynomial (Fin N) ℝ)
    (a : EuclideanSpace ℝ (Fin N)) :
    polynomialFirstJet (P - Q) a = polynomialFirstJet P a - polynomialFirstJet Q a := by
  ext v
  simp [polynomialFirstJet, polynomialTranslate, Finset.sum_sub_distrib, sub_mul]



lemma polynomialFirstJet_continuous {N : ℕ} (P : MvPolynomial (Fin N) ℝ) :
    Continuous (polynomialFirstJet P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
      have hj : polynomialFirstJet (N := N) (MvPolynomial.C c) = 0 := by
        funext a
        simp [polynomialFirstJet, polynomialTranslate, MvPolynomial.coeff_C,
          eq_comm, Finsupp.single_eq_zero]
      rw [hj]
      exact continuous_const
  | add P Q hP hQ =>
      have hj : polynomialFirstJet (P + Q) = polynomialFirstJet P + polynomialFirstJet Q := by
        funext a
        exact polynomialFirstJet_add P Q a
      rw [hj]
      exact hP.add hQ
  | mul_X P j hP =>
      have hj : polynomialFirstJet (P * MvPolynomial.X j) = fun a ↦
          (a j) • polynomialFirstJet P a +
            (MvPolynomial.eval (fun i ↦ a i) P) •
              (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N ↦ ℝ) j) := by
        funext a
        exact polynomialFirstJet_mul_X P a j
      rw [hj]
      have heval : Continuous (fun a : EuclideanSpace ℝ (Fin N) ↦
          MvPolynomial.eval (fun i ↦ a i) P) :=
        (AnalyticOnNhd.eval_continuousLinearMap'
          (fun i : Fin N ↦ (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N ↦ ℝ) i)) P).continuous
      exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N ↦ ℝ) j).continuous.smul hP).add
        (heval.smul continuous_const)



end HolomorphicAnosov
