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

/-- Mathlib finite-product degree calculation for the monomials used in Journé's finite jet polynomial. (Journé, 1988) -/
theorem monomial_totalDegree_le
    {N j : ℕ} (r : Fin j → Fin N) :
    (∏ i : Fin j, (MvPolynomial.X (r i) : MvPolynomial (Fin N) ℝ)).totalDegree ≤ j := by
  calc
    _ ≤ ∑ i : Fin j, (MvPolynomial.X (r i) : MvPolynomial (Fin N) ℝ).totalDegree := by
      simpa using
        (MvPolynomial.totalDegree_finsetProd (Finset.univ : Finset (Fin j))
          (fun i : Fin j ↦ (MvPolynomial.X (r i) : MvPolynomial (Fin N) ℝ)))
    _ = j := by simp

end HolomorphicAnosov.JourneLeafPolynomialApproximation
