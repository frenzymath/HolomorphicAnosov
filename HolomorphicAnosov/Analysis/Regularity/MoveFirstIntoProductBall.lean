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

/-- Source: J1's shrinking of the common product neighborhood; the product
metric is the maximum metric, so moving one component by half the radius stays
inside the original ball. -/
theorem move_first_into_product_ball
    {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {z₀ z : E × F} {x : E} {R : ℝ}
    (hz : z ∈ Metric.ball z₀ (R / 2)) (hx : x ∈ Metric.ball z.1 (R / 2)) :
    (x, z.2) ∈ Metric.ball z₀ R := by
  change dist (x, z.2) z₀ < R
  have hxz : dist (x, z.2) z < R / 2 := by
    simpa only [Metric.mem_ball, Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using hx
  calc
    dist (x, z.2) z₀ ≤ dist (x, z.2) z + dist z z₀ := dist_triangle _ _ _
    _ < R / 2 + R / 2 := add_lt_add hxz hz
    _ = R := add_halves R

end HolomorphicAnosov.JourneLeafPolynomialApproximation
