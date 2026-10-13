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

set_option backward.isDefEq.respectTransparency false in
/-- Source: J1, the assumed jointly continuous first leaf jets. The derivatives
of the actual framed plaques are jointly continuous in both graph-box parameters. -/
theorem graphBox_plaque_derivative_continuousOn
    {d c N n : ℕ} {α : ℝ} {Ω : Set (Block N)}
    (b : GraphBox d c N n α Ω) (hn : 1 ≤ n) :
    ContinuousOn (fun z : Block d × Block c ↦ fderiv ℝ (b.plaque z.2) z.1)
      (Metric.ball 0 b.leafRadius ×ˢ Metric.ball 0 b.transverseRadius) := by
  have hp : ContinuousOn
      (fun z : Block d × Block c ↦
        (ContinuousLinearMap.id ℝ (Block d)).prod (fderiv ℝ (b.graph z.2) z.1))
      (Metric.ball 0 b.leafRadius ×ˢ Metric.ball 0 b.transverseRadius) := by
    exact (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp_continuousOn
      (continuousOn_const.prodMk b.first_jet_continuous)
  apply (continuousOn_const.clm_comp hp).congr
  intro z hz
  exact (graphBox_plaque_hasFDerivAt b hn hz.2 hz.1).fderiv

end HolomorphicAnosov.JourneLeafPolynomialApproximation
