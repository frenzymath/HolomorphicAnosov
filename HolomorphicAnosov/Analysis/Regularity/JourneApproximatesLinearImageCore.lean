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

open scoped NNReal in
/-- Source: Glöckner, Theorem 5.3(d), and the same strict inner-ball
construction in J1. A linear approximation on an open source ball gives a
common ball in the image of its actual local inverse chart. -/
theorem approximates_linear_image_core
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (a : E) (A : E ≃L[ℝ] F) (r : ℝ) (hr : 0 < r)
    (c : ℝ≥0)
    (hc : Subsingleton E ∨ c < ‖A.symm.toContinuousLinearMap‖₊⁻¹)
    (hf : ApproximatesLinearOn f A.toContinuousLinearMap (Metric.ball a r) c) :
    ∃ e : OpenPartialHomeomorph E F,
      (e : E → F) = f ∧ e.source = Metric.ball a r ∧
      Metric.ball (f a)
        (((‖A.symm.toContinuousLinearMap‖₊⁻¹ : ℝ) - (c : ℝ)) * (r / 2)) ⊆
        e.target := by
  let e := hf.toOpenPartialHomeomorph f (Metric.ball a r) hc Metric.isOpen_ball
  refine ⟨e, rfl, rfl, ?_⟩
  exact Metric.ball_subset_closedBall.trans
    (hf.closedBall_subset_target hc Metric.isOpen_ball (le_of_lt (half_pos hr))
      (Metric.closedBall_subset_ball (half_lt_self hr)))

end HolomorphicAnosov.JourneLeafPolynomialApproximation
