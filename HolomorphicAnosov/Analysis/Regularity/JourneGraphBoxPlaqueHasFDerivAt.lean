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

set_option backward.isDefEq.respectTransparency false in
/-- Source: Journé p.188, marked plaque coordinates, and J1 of the current DAG.
The original graph plaque derivative has first coordinate equal to its input after
applying the inverse of the box's actual linear frame. -/
theorem graphBox_plaque_hasFDerivAt
    {d c N n : ℕ} {α : ℝ} {Ω : Set (Block N)}
    (b : GraphBox d c N n α Ω) (hn : 1 ≤ n)
    {w : Block c} (hw : w ∈ Metric.ball 0 b.transverseRadius)
    {x : Block d} (hx : x ∈ Metric.ball 0 b.leafRadius) :
    HasFDerivAt (b.plaque w)
      (b.frame.toContinuousLinearMap.comp
        ((ContinuousLinearMap.id ℝ (Block d)).prod (fderiv ℝ (b.graph w) x))) x := by
  obtain ⟨K, hK, hg⟩ := b.graph_bounds
  have hd : DifferentiableAt ℝ (b.graph w) x :=
    (((hg w hw).1.differentiableOn (by simpa using (show n ≠ 0 by omega))) x hx).differentiableAt
      (Metric.isOpen_ball.mem_nhds hx)
  simpa only [GraphBox.plaque, Function.comp_def, id_eq] using!
    ((b.frame.hasFDerivAt.comp x ((hasFDerivAt_id x).prodMk hd.hasFDerivAt)).const_add b.base)

end HolomorphicAnosov.JourneLeafPolynomialApproximation
