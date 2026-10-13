import HolomorphicAnosov.Analysis.Regularity.PolynomialBallDerivativeEstimate
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Monad
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

lemma polynomialTranslate_pderiv {N : ℕ} (P : MvPolynomial (Fin N) ℝ)
    (a : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    polynomialTranslate (MvPolynomial.pderiv i P) a =
      MvPolynomial.pderiv i (polynomialTranslate P a) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [polynomialTranslate]
  | add P Q hP hQ =>
      change MvPolynomial.eval₂ MvPolynomial.C
        (fun i ↦ MvPolynomial.C (a i) + MvPolynomial.X i) _ = _ at hP hQ
      simp [polynomialTranslate, -MvPolynomial.eval₂Hom_C_eq_bind₁, hP, hQ]
  | mul_X P j hP =>
      change MvPolynomial.eval₂ MvPolynomial.C
        (fun i ↦ MvPolynomial.C (a i) + MvPolynomial.X i) _ = _ at hP
      by_cases hij : i = j
      · subst i
        simp [polynomialTranslate, -MvPolynomial.eval₂Hom_C_eq_bind₁, hP]
      · simp [polynomialTranslate, -MvPolynomial.eval₂Hom_C_eq_bind₁, hP, Ne.symm hij]



lemma polynomial_pderiv_eval {N : ℕ} (P : MvPolynomial (Fin N) ℝ)
    (a : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    MvPolynomial.eval (fun j ↦ a j) (MvPolynomial.pderiv i P) =
      (polynomialTranslate P a).coeff (Finsupp.single i 1) := by
  rw [← polynomialTranslate_coeff_zero, polynomialTranslate_pderiv,
    MvPolynomial.coeff_pderiv]
  simp



lemma polynomial_pderiv_degree {N n : ℕ} (P : MvPolynomial (Fin N) ℝ)
    (hP : P.totalDegree ≤ n + 1) (i : Fin N) :
    (MvPolynomial.pderiv i P).totalDegree ≤ n := by
  classical
  rw [MvPolynomial.totalDegree]
  apply Finset.sup_le
  intro β hβ
  have hcoef : (MvPolynomial.pderiv i P).coeff β ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hβ
  rw [MvPolynomial.coeff_pderiv] at hcoef
  have hmem : β + Finsupp.single i 1 ∈ P.support := by
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    rw [hz, zero_mul] at hcoef
    exact hcoef rfl
  have hdegree := (MvPolynomial.le_totalDegree hmem).trans hP
  have hsum : (β + Finsupp.single i 1).sum (fun _ k ↦ k) =
      β.sum (fun _ k ↦ k) + 1 := by
    simp [Finsupp.sum_add_index]
  rw [hsum] at hdegree
  omega



end HolomorphicAnosov
