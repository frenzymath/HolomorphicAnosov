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
open scoped Manifold ContDiff Topology _root_.Topology NNReal

namespace HolomorphicAnosov.JointRealC1Scratch
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- W05's product-partial kernel, with arbitrary real normed codomain. Mathlib's
`hasStrictFDerivAt_uncurry_coprod` derives the joint derivative from the actual
partials on a neighborhood. Its value at `(h,τ)` is `Y h + τ • V`. No completeness
or finite-dimensionality is required, so zero-dimensional spaces are included. -/
theorem joint_hasFDerivAt_of_partials
    (α : E → ℝ → F) (Y : E → ℝ → E →L[ℝ] F) (V : E → ℝ → F)
    (U : Set E) (I : Set ℝ) (hU : IsOpen U) (hI : IsOpen I)
    (hspace : ∀ x ∈ U, ∀ t ∈ I, HasFDerivAt (fun q ↦ α q t) (Y x t) x)
    (htime : ∀ x ∈ U, ∀ t ∈ I, HasDerivAt (α x) (V x t) t)
    (hY : ContinuousOn (fun p : E × ℝ ↦ Y p.1 p.2) (U ×ˢ I))
    (hV : ContinuousOn (fun p : E × ℝ ↦ V p.1 p.2) (U ×ˢ I)) :
    ∀ p ∈ U ×ˢ I, HasFDerivAt (fun p : E × ℝ ↦ α p.1 p.2)
      ((Y p.1 p.2).coprod (ContinuousLinearMap.toSpanSingleton ℝ (V p.1 p.2))) p := by
  intro p hp
  have hnh : U ×ˢ I ∈ 𝓝 p := (hU.prod hI).mem_nhds hp
  apply (hasStrictFDerivAt_uncurry_coprod
    (f := α) (f₁ := Y) (f₂ := fun x t ↦ ContinuousLinearMap.toSpanSingleton ℝ (V x t))
    (u := p) ?_ ?_ ?_ ?_).hasFDerivAt
  · filter_upwards [hnh] with q hq
    exact hspace q.1 hq.1 q.2 hq.2
  · filter_upwards [hnh] with q hq
    exact (htime q.1 hq.1 q.2 hq.2).hasFDerivAt
  · exact hY.continuousAt hnh
  · exact (ContinuousLinearMap.toSpanSingletonLIE ℝ F).continuous.continuousAt.comp
      (hV.continuousAt hnh)

end HolomorphicAnosov.JointRealC1Scratch
