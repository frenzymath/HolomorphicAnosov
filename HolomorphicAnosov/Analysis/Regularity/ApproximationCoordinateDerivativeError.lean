import HolomorphicAnosov.Analysis.Regularity.PolynomialBallDerivativeEstimate
import HolomorphicAnosov.Analysis.Regularity.ApproximationPolynomialDifferenceBound
import HolomorphicAnosov.Analysis.Regularity.ApproximationPolynomialJetComparison
import HolomorphicAnosov.Analysis.Regularity.ApproximationRemainderFDerivAt
import HolomorphicAnosov.Analysis.Regularity.PolynomialFirstJet
import HolomorphicAnosov.Analysis.Regularity.PolynomialFirstJetSingle
import HolomorphicAnosov.Analysis.Regularity.PolynomialTranslateDerivatives
import HolomorphicAnosov.Analysis.Regularity.HolderOnWithNormBound
import HolomorphicAnosov.Analysis.Regularity.EuclideanDualCoordinate
import HolomorphicAnosov.Analysis.Regularity.EuclideanDualNorm
import HolomorphicAnosov.Analysis.Regularity.IteratedFDerivSuccDifferenceBound
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
import HolomorphicAnosov.Analysis.Regularity.ApproximationFirstJetHasFDerivAt
import HolomorphicAnosov.Analysis.Regularity.ApproximationFirstJetComparison

namespace HolomorphicAnosov

open Filter
open scoped Topology _root_.Topology

lemma approximation_coordinate_derivative_error (N n : ℕ) (hN : 1 ≤ N)
    (hn : 1 ≤ n) (s : ℝ) (hs : 1 < s) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (h : EuclideanSpace ℝ (Fin N) → ℝ) (P Q : MvPolynomial (Fin N) ℝ)
        (a b : EuclideanSpace ℝ (Fin N)) (C r : ℝ),
        P.totalDegree ≤ n → Q.totalDegree ≤ n → 0 ≤ C → 0 < r → dist b a < r / 2 →
        (∀ y ∈ Metric.ball a r,
          |h y - MvPolynomial.eval (fun i ↦ y i) P| ≤ C * ‖y - a‖ ^ s) →
        (∀ y ∈ Metric.ball b r,
          |h y - MvPolynomial.eval (fun i ↦ y i) Q| ≤ C * ‖y - b‖ ^ s) →
        ∀ i : Fin N,
          |fderiv ℝ h b (PiLp.single 2 i (1 : ℝ)) -
            MvPolynomial.eval (fun j ↦ b j) (MvPolynomial.pderiv i P)| ≤
              D * C * ‖b - a‖ ^ (s - 1) := by
  obtain ⟨D, hD, hest⟩ := approximation_firstJet_comparison N n hN hn s (by linarith)
  refine ⟨D, hD, ?_⟩
  intro h P Q a b C r hPdeg hQdeg hC hr hdist hP hQ i
  have hbeq : fderiv ℝ h b = polynomialFirstJet Q b :=
    (approximation_firstJet_hasFDerivAt h Q b C r s hC hr hs hQ).fderiv
  by_cases hba : b = a
  · subst b
    have hpeq : fderiv ℝ h a = polynomialFirstJet P a :=
      (approximation_firstJet_hasFDerivAt h P a C r s hC hr hs hP).fderiv
    rw [hpeq, polynomialFirstJet_single]
    simp only [sub_self, abs_zero, norm_zero]
    positivity
  have hρ : 0 < dist b a := dist_pos.mpr hba
  have hρr : 2 * dist b a < r := by linarith
  have hnorm : ‖polynomialFirstJet Q b - polynomialFirstJet P b‖ ≤
      D * C * ‖b - a‖ ^ (s - 1) := by
    rw [norm_sub_rev]
    simpa only [dist_eq_norm] using
      hest h Q P b a C (dist b a) hQdeg hPdeg hC hρ le_rfl
        (fun y hy ↦ hQ y ((Metric.ball_subset_ball hρr.le) hy))
        (fun y hy ↦ hP y ((Metric.ball_subset_ball hρr.le) hy))
  rw [hbeq, ← polynomialFirstJet_single]
  have he := (polynomialFirstJet Q b - polynomialFirstJet P b).le_opNorm
    (PiLp.single 2 i (1 : ℝ))
  simpa only [sub_apply, Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one] using
    he.trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))

end HolomorphicAnosov
