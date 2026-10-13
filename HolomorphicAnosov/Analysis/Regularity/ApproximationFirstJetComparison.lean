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

namespace HolomorphicAnosov

open Filter
open scoped Topology _root_.Topology

lemma approximation_firstJet_comparison (N n : ℕ) (hN : 1 ≤ N) (hn : 1 ≤ n)
    (s : ℝ) (hs : 0 ≤ s) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (h : EuclideanSpace ℝ (Fin N) → ℝ) (P Q : MvPolynomial (Fin N) ℝ)
        (a b : EuclideanSpace ℝ (Fin N)) (C ρ : ℝ),
        P.totalDegree ≤ n → Q.totalDegree ≤ n → 0 ≤ C → 0 < ρ → dist a b ≤ ρ →
        (∀ y ∈ Metric.ball a (2 * ρ),
          |h y - MvPolynomial.eval (fun i ↦ y i) P| ≤ C * ‖y - a‖ ^ s) →
        (∀ y ∈ Metric.ball b (2 * ρ),
          |h y - MvPolynomial.eval (fun i ↦ y i) Q| ≤ C * ‖y - b‖ ^ s) →
        ‖polynomialFirstJet Q a - polynomialFirstJet P a‖ ≤ D * C * ρ ^ (s - 1) := by
  obtain ⟨L, hL, hest⟩ := approximation_polynomial_jet_comparison N n hN s hs
  have hNr : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  refine ⟨N * L, mul_pos hNr hL, ?_⟩
  intro h P Q a b C ρ hPdeg hQdeg hC hρ hab hP hQ
  rw [← polynomialFirstJet_sub]
  calc
    ‖polynomialFirstJet (Q - P) a‖ ≤ N * (L * C * ρ ^ (s - 1)) := by
      apply polynomialFirstJet_norm_bound _ _ _ (by positivity)
      intro i
      have horder : polynomialMultiIndexOrder (Finsupp.single i 1) = 1 := by
        simp [polynomialMultiIndexOrder]
      have hpartial : polynomialPartialAt (Q - P) a (Finsupp.single i 1) =
          polynomialPartialAt Q a (Finsupp.single i 1) -
            polynomialPartialAt P a (Finsupp.single i 1) := by
        simp only [polynomialPartialAt, polynomialTranslate, map_sub,
          MvPolynomial.coeff_sub, mul_sub]
      rw [hpartial]
      simpa only [horder, Nat.cast_one] using
        hest h P Q a b C ρ hPdeg hQdeg hC hρ hab hP hQ
          (Finsupp.single i 1) (by simpa only [horder] using hn)
    _ = N * L * C * ρ ^ (s - 1) := by ring

end HolomorphicAnosov
