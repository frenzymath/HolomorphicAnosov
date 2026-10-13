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
import HolomorphicAnosov.Analysis.Regularity.PolynomialFirstJet
import HolomorphicAnosov.Analysis.Regularity.PolynomialTranslateDerivatives

namespace HolomorphicAnosov

open Filter
open scoped Topology _root_.Topology

lemma polynomialFirstJet_single {N : ℕ} (P : MvPolynomial (Fin N) ℝ)
    (a : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    polynomialFirstJet P a (PiLp.single 2 i (1 : ℝ)) =
      MvPolynomial.eval (fun j ↦ a j) (MvPolynomial.pderiv i P) := by
  classical
  rw [polynomial_pderiv_eval]
  simp [polynomialFirstJet, PiLp.single_apply]

-- The induction exponent drops by precisely one; no Hölder exponent is lost.


end HolomorphicAnosov
