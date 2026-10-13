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

namespace HolomorphicAnosov

open Filter
open scoped Topology _root_.Topology

lemma approximation_firstJet_hasFDerivAt {N : ℕ}
    (h : EuclideanSpace ℝ (Fin N) → ℝ) (P : MvPolynomial (Fin N) ℝ)
    (a : EuclideanSpace ℝ (Fin N)) (C r s : ℝ)
    (hC : 0 ≤ C) (hr : 0 < r) (hs : 1 < s)
    (hf : ∀ y ∈ Metric.ball a r,
      |h y - MvPolynomial.eval (fun i ↦ y i) P| ≤ C * ‖y - a‖ ^ s) :
    HasFDerivAt h (polynomialFirstJet P a) a := by
  have hd := approximation_remainder_hasFDerivAt
    (fun y ↦ h y - MvPolynomial.eval (fun i ↦ y i) P) a C r s hC hr hs hf
  have he := hd.add (polynomial_hasFDerivAt_firstJet P a)
  have hfun : (fun y : EuclideanSpace ℝ (Fin N) ↦
      h y - MvPolynomial.eval (fun i ↦ y i) P) +
      (fun y : EuclideanSpace ℝ (Fin N) ↦ MvPolynomial.eval (fun i ↦ y i) P) = h := by
    funext y
    exact sub_add_cancel _ _
  rw [hfun] at he
  simpa only [zero_add] using he

end HolomorphicAnosov
