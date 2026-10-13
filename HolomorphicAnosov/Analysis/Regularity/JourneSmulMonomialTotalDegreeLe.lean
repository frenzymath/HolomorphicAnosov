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
import HolomorphicAnosov.Analysis.Regularity.JourneMonomialTotalDegreeLe

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation
open Set

/-- A scalar coefficient does not increase the monomial degree. -/
theorem smul_monomial_totalDegree_le
    {N j : ℕ} (c : ℝ) (r : Fin j → Fin N) :
    (c • (∏ i : Fin j,
      (MvPolynomial.X (r i) : MvPolynomial (Fin N) ℝ))).totalDegree ≤ j := by
  exact (MvPolynomial.totalDegree_smul_le c _).trans (monomial_totalDegree_le r)

end HolomorphicAnosov.JourneLeafPolynomialApproximation
