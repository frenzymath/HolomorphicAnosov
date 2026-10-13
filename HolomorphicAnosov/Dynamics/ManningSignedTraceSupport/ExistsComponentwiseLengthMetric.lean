import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.FiniteEdistConnectedComponent
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.ExistsCompatibleMetricPreservingFiniteEdist

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter

open Set Filter _root_.Topology
open scoped BigOperators ENNReal ContDiff Manifold Bundle Classical
noncomputable section

/-- Agent-expanded adapter for Manning's coding application, not a printed Manning theorem. Install the supplied smooth tensor's Riemannian norms and native extended length distance. This distance has the original topology. Cap it using the compact bound. Every pair in one connected component has finite distance, hence retains exactly its native length distance. No connectedness hypothesis or tensor change is introduced. -/
theorem exists_componentwise_length_metric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [t : TopologicalSpace M] [T3Space M] [CompactSpace M]
    [ChartedSpace E M] [IsManifold (modelWithCornersSelf ℝ E) ∞ M]
    (g : Bundle.ContMDiffRiemannianMetric (modelWithCornersSelf ℝ E) ∞ E
      (fun x : M ↦ TangentSpace (modelWithCornersSelf ℝ E) x)) :
    let : Bundle.RiemannianBundle
      (fun x : M ↦ TangentSpace (modelWithCornersSelf ℝ E) x) := ⟨g.toRiemannianMetric⟩
    ∃ m : MetricSpace M, m.toUniformSpace.toTopologicalSpace = t ∧
      ∀ x y : M, y ∈ connectedComponent x →
        @edist M m.toPseudoMetricSpace.toPseudoEMetricSpace.toEDist x y =
          Manifold.riemannianEDist (modelWithCornersSelf ℝ E) x y := by
  let : Bundle.RiemannianBundle
      (fun x : M ↦ TangentSpace (modelWithCornersSelf ℝ E) x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun x : M ↦ TangentSpace (modelWithCornersSelf ℝ E) x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (modelWithCornersSelf ℝ E) M
  obtain ⟨m, htop, hm⟩ := exists_compatible_metric_preserving_finite_edist (X := M)
  refine ⟨m, ?_, ?_⟩
  · exact htop
  · intro x y hy
    exact hm x y (finite_edist_of_mem_connectedComponent hy)


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter
