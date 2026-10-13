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
import HolomorphicAnosov.Analysis.Regularity.JourneGraphBoxPlaqueHasFDerivAt

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation
open Set

open scoped NNReal in
/-- J1's mean-value estimate on a ball contained in the original plaque domain.
No estimate for a totalized graph outside its supplied parameter ball is used. -/
theorem graphBox_approximates_on_ball
    {d c N n : ℕ} {α : ℝ} {Ω : Set (Block N)}
    (b : GraphBox d c N n α Ω) (hn : 1 ≤ n)
    (w : Block c) (x : Block d) (r : ℝ) (D : Block d →L[ℝ] Block N) (ε : ℝ≥0)
    (hbox : ∀ y ∈ Metric.ball x r,
      (y, w) ∈ Metric.ball 0 b.leafRadius ×ˢ Metric.ball 0 b.transverseRadius)
    (hclose : ∀ y ∈ Metric.ball x r, ‖fderiv ℝ (b.plaque w) y - D‖ < ε) :
    ApproximatesLinearOn (b.plaque w) D (Metric.ball x r) ε := by
  intro y hy z hz
  exact (convex_ball x r).norm_image_sub_le_of_norm_fderiv_le'
    (fun t ht ↦ (graphBox_plaque_hasFDerivAt b hn (hbox t ht).2
      (hbox t ht).1).differentiableAt)
    (fun t ht ↦ (hclose t ht).le) hz hy

end HolomorphicAnosov.JourneLeafPolynomialApproximation
