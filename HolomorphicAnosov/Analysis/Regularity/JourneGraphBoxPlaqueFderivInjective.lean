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

/-- Source: Journé p.188 and J1: every original graph plaque is an immersion;
projection to its first parameter recovers a vector from the differential. -/
theorem graphBox_plaque_fderiv_injective
    {d c N n : ℕ} {α : ℝ} {Ω : Set (Block N)}
    (b : GraphBox d c N n α Ω) (hn : 1 ≤ n)
    {w : Block c} (hw : w ∈ Metric.ball 0 b.transverseRadius)
    {x : Block d} (hx : x ∈ Metric.ball 0 b.leafRadius) :
    Function.Injective (fderiv ℝ (b.plaque w) x) := by
  rw [(graphBox_plaque_hasFDerivAt b hn hw hx).fderiv]
  intro v v' hv
  exact congrArg Prod.fst (b.frame.injective hv)

end HolomorphicAnosov.JourneLeafPolynomialApproximation
