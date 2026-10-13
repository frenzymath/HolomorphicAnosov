import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue
import HolomorphicAnosov.Analysis.Flow.JointDerivative

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology NNReal

namespace SmoothFlowBootstrap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The concrete first derivative agrees with the C1 producer's canonical
coproduct operator, so that existing source witnesses bind without a new
first-derivative or spatial-smoothness premise. -/
theorem jointDerivative_eq_coprod
    (Y : E × ℝ → E →L[ℝ] E) (V : E × ℝ → E) (p : E × ℝ) :
    jointDerivative Y V p = (Y p).coprod (ContinuousLinearMap.toSpanSingleton ℝ (V p)) := by
  apply ContinuousLinearMap.ext
  intro q
  simp [jointDerivative, ContinuousLinearMap.coprod_apply]

end SmoothFlowBootstrap
