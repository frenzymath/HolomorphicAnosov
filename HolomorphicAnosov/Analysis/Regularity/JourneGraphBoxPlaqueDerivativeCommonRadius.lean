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
import HolomorphicAnosov.Analysis.Regularity.JourneGraphBoxPlaqueDerivativeUniformNeighborhood
import HolomorphicAnosov.Analysis.Regularity.MoveFirstIntoProductBall

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation
open Set

set_option backward.isDefEq.respectTransparency false in
/-- Source: J1. A single radius controls leaf points around every marked
centre in a smaller graph-box neighborhood, including varying transverse labels. -/
theorem graphBox_plaque_derivative_common_radius
    {d c N n : ℕ} {α : ℝ} {Ω : Set (Block N)}
    (b : GraphBox d c N n α Ω) (hn : 1 ≤ n)
    {z₀ : Block d × Block c}
    (hz₀ : z₀ ∈ Metric.ball 0 b.leafRadius ×ˢ Metric.ball 0 b.transverseRadius)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ Metric.ball z₀ r, ∀ x ∈ Metric.ball z.1 r,
      (x, z.2) ∈ Metric.ball 0 b.leafRadius ×ˢ Metric.ball 0 b.transverseRadius ∧
      ‖fderiv ℝ (b.plaque z.2) x - fderiv ℝ (b.plaque z₀.2) z₀.1‖ < ε := by
  obtain ⟨R, hR, hbox, hclose⟩ :=
    graphBox_plaque_derivative_uniform_neighborhood b hn hz₀ hε
  refine ⟨R / 2, half_pos hR, ?_⟩
  intro z hz x hx
  have hpair := move_first_into_product_ball hz hx
  refine ⟨hbox hpair, ?_⟩
  simpa only using! hclose (x, z.2) hpair

end HolomorphicAnosov.JourneLeafPolynomialApproximation
