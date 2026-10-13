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

namespace HolomorphicAnosov

open Filter
open scoped Topology _root_.Topology

lemma polynomialTranslate_coeff_zero {N : ℕ} (P : MvPolynomial (Fin N) ℝ)
    (a : EuclideanSpace ℝ (Fin N)) :
    (polynomialTranslate P a).coeff 0 = MvPolynomial.eval (fun i ↦ a i) P := by
  change MvPolynomial.constantCoeff (polynomialTranslate P a) = _
  unfold polynomialTranslate
  have heq : MvPolynomial.constantCoeff.comp
      (MvPolynomial.eval₂Hom MvPolynomial.C (fun i ↦ MvPolynomial.C (a i) + MvPolynomial.X i)) =
      MvPolynomial.eval (fun i ↦ a i) := by
    ext i <;> simp
  exact RingHom.congr_fun heq P

-- This finite sum is the unnormalized first polynomial jet in the original L2 norm.


end HolomorphicAnosov
