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
import HolomorphicAnosov.Analysis.Regularity.JourneContDiffAtDerivativeCloseOnBall

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation
open Set

open scoped NNReal in
/-- Source: J1, the mean-value bound on a convex open ball. The derivative
neighborhood supplies the required two-point approximation with any positive tolerance. -/
theorem contDiffAt_approximates_on_ball
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} (hn : 1 ≤ n) {f : E → F} {a : E} {A : E →L[ℝ] F}
    (hf : ContDiffAt ℝ n f a) (hA : HasFDerivAt f A a)
    (c : ℝ≥0) (hc : 0 < c) :
    ∃ r : ℝ, 0 < r ∧ ApproximatesLinearOn f A (Metric.ball a r) c := by
  obtain ⟨r, hr, hb⟩ := contDiffAt_derivative_close_on_ball hn hf hA c hc
  refine ⟨r, hr, ?_⟩
  intro x hx y hy
  exact (convex_ball a r).norm_image_sub_le_of_norm_fderiv_le'
    (fun z hz ↦ (hb z hz).1) (fun z hz ↦ (hb z hz).2.le) hy hx

end HolomorphicAnosov.JourneLeafPolynomialApproximation
