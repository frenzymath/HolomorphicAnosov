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
import HolomorphicAnosov.Analysis.Regularity.JourneSmulMonomialTotalDegreeLe

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation
open Set

/-- A finite sum of scalar monomials indexed by all orders up to `n` has
ordinary total degree at most `n`; this is the finite carrier estimate used by
Journé's ambient jet polynomial. -/
theorem finite_monomial_sum_totalDegree_le
    {N n : ℕ} (coeff : (j : Fin (n + 1)) → (Fin j → Fin N) → ℝ) :
    (∑ j : Fin (n + 1), ∑ r : Fin j → Fin N,
      coeff j r • (∏ i : Fin j, (MvPolynomial.X (r i) : MvPolynomial (Fin N) ℝ))).totalDegree ≤ n := by
  have hinner : ∀ j : Fin (n + 1),
      (∑ r : Fin j → Fin N,
        coeff j r • (∏ i : Fin j, (MvPolynomial.X (r i) : MvPolynomial (Fin N) ℝ))).totalDegree ≤ j := by
    intro j
    apply MvPolynomial.totalDegree_finsetSum_le
    intro r hr
    exact smul_monomial_totalDegree_le (coeff j r) r
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  exact (hinner j).trans (Nat.le_of_lt_succ j.isLt)

end HolomorphicAnosov.JourneLeafPolynomialApproximation
