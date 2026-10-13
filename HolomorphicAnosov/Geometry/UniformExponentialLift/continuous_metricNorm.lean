import HolomorphicAnosov.Geometry.UniformExponentialLift.base
import HolomorphicAnosov.Geometry.UniformExponentialLift.local_metric_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.compact_metric_tube

noncomputable section

namespace HolomorphicAnosov
namespace ExponentialLift

open Bundle Set TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The Riemannian norm is continuous on the tangent bundle. -/
theorem continuous_metricNorm
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _)) :
    Continuous (fun z : TangentBundle 𝓘(ℝ, E) M ↦ metricNorm g z.proj z.snd) := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.toContinuousRiemannianMetric.toRiemannianMetric⟩
  have h : Continuous (fun z : TangentBundle 𝓘(ℝ, E) M ↦ inner ℝ z.snd z.snd) :=
    continuous_id.inner_bundle continuous_id
  exact Real.continuous_sqrt.comp h


end ExponentialLift
end HolomorphicAnosov
