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
import HolomorphicAnosov.Analysis.Regularity.JourneMonomialEvalNormLe

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation
open Set

/-- The corresponding finite polynomial obeys the sum of monomial bounds on a
bounded graph-box coordinate vector. -/
theorem finite_monomial_sum_eval_norm_le
    {N n : ℕ} (coeff : (j : Fin (n + 1)) → (Fin j → Fin N) → ℝ)
    (x : Fin N → ℝ) :
    ‖MvPolynomial.eval x
      (∑ j : Fin (n + 1), ∑ r : Fin j → Fin N,
        coeff j r • (∏ i : Fin j, (MvPolynomial.X (r i) : MvPolynomial (Fin N) ℝ)))‖ ≤
      ∑ j : Fin (n + 1), ∑ r : Fin j → Fin N,
        ‖coeff j r‖ * ∏ i : Fin j, ‖x (r i)‖ := by
  rw [MvPolynomial.eval_sum]
  calc
    _ ≤ ∑ j : Fin (n + 1), ‖MvPolynomial.eval x
        (∑ r : Fin j → Fin N,
          coeff j r • (∏ i : Fin j,
            (MvPolynomial.X (r i) : MvPolynomial (Fin N) ℝ)))‖ := by
      exact norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [MvPolynomial.eval_sum]
      calc
        _ ≤ ∑ r : Fin j → Fin N, ‖MvPolynomial.eval x
            (coeff j r • (∏ i : Fin j,
              (MvPolynomial.X (r i) : MvPolynomial (Fin N) ℝ)))‖ := by
          exact norm_sum_le _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro r hr
          exact monomial_eval_norm_le (coeff j r) r x

end HolomorphicAnosov.JourneLeafPolynomialApproximation
