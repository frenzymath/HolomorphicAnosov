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
import HolomorphicAnosov.Analysis.Regularity.JourneGraphBoxPlaqueDerivativeContinuousOn

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation
open Set

open scoped Topology in
/-- Source: J1, uniform control of the first leaf derivatives after shrinking
both graph-box parameters. This controls transverse labels as well as leaf points;
it assumes no transverse differentiability. -/
theorem graphBox_plaque_derivative_uniform_neighborhood
    {d c N n : ℕ} {α : ℝ} {Ω : Set (Block N)}
    (b : GraphBox d c N n α Ω) (hn : 1 ≤ n)
    {z₀ : Block d × Block c}
    (hz₀ : z₀ ∈ Metric.ball 0 b.leafRadius ×ˢ Metric.ball 0 b.transverseRadius)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧
      Metric.ball z₀ r ⊆ Metric.ball 0 b.leafRadius ×ˢ Metric.ball 0 b.transverseRadius ∧
      ∀ z ∈ Metric.ball z₀ r,
        ‖fderiv ℝ (b.plaque z.2) z.1 - fderiv ℝ (b.plaque z₀.2) z₀.1‖ < ε := by
  have hopen : IsOpen (Metric.ball (0 : Block d) b.leafRadius ×ˢ
      Metric.ball (0 : Block c) b.transverseRadius) :=
    Metric.isOpen_ball.prod Metric.isOpen_ball
  have hc := (graphBox_plaque_derivative_continuousOn b hn).continuousAt
    (hopen.mem_nhds hz₀)
  have he : ∀ᶠ z in 𝓝 z₀,
      ‖fderiv ℝ (b.plaque z.2) z.1 - fderiv ℝ (b.plaque z₀.2) z₀.1‖ < ε :=
    (hc.sub_const _).norm.eventually (gt_mem_nhds (by simpa using hε))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (hopen.mem_nhds hz₀) he)
  exact ⟨r, hr, fun z hz ↦ (hball hz).1, fun z hz ↦ (hball hz).2⟩

end HolomorphicAnosov.JourneLeafPolynomialApproximation
