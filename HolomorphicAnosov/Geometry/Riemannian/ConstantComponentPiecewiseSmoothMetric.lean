import HolomorphicAnosov.Topology.ConstantComponentMetric
import HolomorphicAnosov.Geometry.Riemannian.FiniteRiemannianEDistConnectedComponent
import HolomorphicAnosov.Geometry.Riemannian.RiemannianEDistEqPiecewiseSmooth
import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothRiemannianEDist
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

open Set
open scoped Manifold ContDiff ENNReal Bundle
namespace HolomorphicAnosov

/-- A compact smooth Riemannian manifold admits a metric inducing its topology that equals its
piecewise-smooth Riemannian distance on each connected component and a fixed positive constant
between distinct components. -/
theorem exists_constant_component_piecewiseSmooth_metric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [t : TopologicalSpace M] [T3Space M] [CompactSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (h : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)) :
    ∃ (d : MetricSpace M) (D : ℝ), 0 < D ∧
      d.toUniformSpace.toTopologicalSpace = t ∧
      (∀ x y : M, y ∈ @connectedComponent M t x →
        ENNReal.ofReal (d.dist x y) = piecewiseSmoothRiemannianEDist h x y) ∧
      (∀ x y : M, y ∉ @connectedComponent M t x → d.dist x y = D) := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨h.inner, h.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) M
  obtain ⟨d, D, hD, htop, hcomp, hsep⟩ := exists_constant_component_metric
    (fun (x y : M) hxy => mem_connectedComponent_of_riemannianEDist_ne_top 𝓘(ℝ, E) hxy)
  refine ⟨d, D, hD, htop, ?_, hsep⟩
  intro x y hxy
  exact (hcomp x y hxy).trans (riemannianEDist_eq_piecewiseSmoothRiemannianEDist h x y)

end HolomorphicAnosov
