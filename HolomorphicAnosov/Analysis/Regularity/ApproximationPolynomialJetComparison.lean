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
import HolomorphicAnosov.Analysis.Regularity.ApproximationPolynomialDifferenceBound

namespace HolomorphicAnosov

open Filter
open scoped Topology _root_.Topology

lemma approximation_polynomial_jet_comparison (N n : ℕ) (hN : 1 ≤ N)
    (s : ℝ) (hs : 0 ≤ s) :
    ∃ L : ℝ, 0 < L ∧
      ∀ (h : EuclideanSpace ℝ (Fin N) → ℝ) (P Q : MvPolynomial (Fin N) ℝ)
        (a b : EuclideanSpace ℝ (Fin N)) (C ρ : ℝ),
        P.totalDegree ≤ n → Q.totalDegree ≤ n → 0 ≤ C → 0 < ρ → dist a b ≤ ρ →
        (∀ y ∈ Metric.ball a (2 * ρ),
          |h y - MvPolynomial.eval (fun i ↦ y i) P| ≤ C * ‖y - a‖ ^ s) →
        (∀ y ∈ Metric.ball b (2 * ρ),
          |h y - MvPolynomial.eval (fun i ↦ y i) Q| ≤ C * ‖y - b‖ ^ s) →
        ∀ β : Fin N →₀ ℕ, polynomialMultiIndexOrder β ≤ n →
          |polynomialPartialAt Q a β - polynomialPartialAt P a β| ≤
            L * C * ρ ^ (s - (polynomialMultiIndexOrder β : ℝ)) := by
  obtain ⟨K, hK, hest⟩ := polynomial_ball_derivative_estimate N n hN
  refine ⟨2 * K * (2 : ℝ) ^ s, by positivity, ?_⟩
  intro h P Q a b C ρ hPdeg hQdeg hC hρ hab hP hQ β hβ
  have hdeg : (Q - P).totalDegree ≤ n :=
    (MvPolynomial.totalDegree_sub Q P).trans (max_le hQdeg hPdeg)
  have hM : 0 ≤ 2 * C * (2 * ρ) ^ s := by positivity
  have hd := (hest (Q - P) hdeg a ρ hρ β hβ).2
    (2 * C * (2 * ρ) ^ s) hM
    (approximation_polynomial_difference_bound h P Q a b C ρ s hC hρ hs hab hP hQ)
  have hpartial : polynomialPartialAt (Q - P) a β =
      polynomialPartialAt Q a β - polynomialPartialAt P a β := by
    simp only [polynomialPartialAt, polynomialTranslate, map_sub, MvPolynomial.coeff_sub,
      mul_sub]
  rw [hpartial] at hd
  calc
    |polynomialPartialAt Q a β - polynomialPartialAt P a β| ≤
        K * ρ ^ (-(polynomialMultiIndexOrder β : ℝ)) *
          (2 * C * (2 * ρ) ^ s) := hd
    _ = (2 * K * (2 : ℝ) ^ s) * C *
        ρ ^ (s - (polynomialMultiIndexOrder β : ℝ)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hρ.le,
        Real.rpow_sub hρ]
      rw [Real.rpow_neg hρ.le]
      ring

-- A higher-than-linear pointwise remainder has zero first derivative at its centre.


end HolomorphicAnosov
