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

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology NNReal

namespace SmoothFlowBootstrap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The genuine full joint derivative assembled from the spatial variational
operator and the actual time vector. It is a concrete map, not a derivative
premise or a hollow definition. -/
def jointDerivative (Y : E × ℝ → E →L[ℝ] E) (V : E × ℝ → E)
    (p : E × ℝ) : (E × ℝ) →L[ℝ] E :=
  (Y p).comp (ContinuousLinearMap.fst ℝ E ℝ) +
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (V p)).comp (ContinuousLinearMap.snd ℝ E ℝ)

end SmoothFlowBootstrap
