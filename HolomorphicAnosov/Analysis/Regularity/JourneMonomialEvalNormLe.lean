import HolomorphicAnosov.Analysis.BilinearHolderBound
import HolomorphicAnosov.Analysis.CompositionHolderBound
import HolomorphicAnosov.Analysis.Regularity.PolynomialBallDerivativeEstimate
import HolomorphicAnosov.Analysis.Regularity.PolynomialMeasurableSubsetDerivativeEstimate
import HolomorphicAnosov.Analysis.WellsLipschitzPerturbationSmoothInverse
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import HolomorphicAnosov.Analysis.Regularity.GraphFoliationData
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.Prod

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation
open Set

/-- Evaluation of one finite jet monomial obeys the product norm bound used on bounded graph boxes. -/
theorem monomial_eval_norm_le
    {N j : ℕ} (c : ℝ) (r : Fin j → Fin N) (x : Fin N → ℝ) :
    ‖MvPolynomial.eval x
      (c • (∏ i : Fin j, (MvPolynomial.X (r i) : MvPolynomial (Fin N) ℝ)))‖ ≤
      ‖c‖ * ∏ i : Fin j, ‖x (r i)‖ := by
  rw [MvPolynomial.smul_eval, MvPolynomial.eval_prod]
  simp only [MvPolynomial.eval_X, norm_mul, norm_prod]
  exact le_rfl

end HolomorphicAnosov.JourneLeafPolynomialApproximation
