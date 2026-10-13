import HolomorphicAnosov.Dynamics.Bowen.BowenBasicSetMarkovCoding
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.ExistsComponentwiseLengthMetric

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set Filter _root_.Topology
open scoped BigOperators ENNReal ContDiff Manifold Bundle Classical
noncomputable section

/-- A compact smooth Riemannian manifold admits a compatible metric whose distance agrees with its native Riemannian length distance on each connected component. -/
theorem original_metric_provider_premise
    {n : ℕ} {M : Type*} [tM : TopologicalSpace M] [T3Space M] [CompactSpace M]
    [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    (h : Bundle.ContMDiffRiemannianMetric
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞
      (EuclideanSpace ℝ (Fin n))
      (fun x : M => TangentSpace
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x)) :
    letI : Bundle.RiemannianBundle
      (fun x : M => TangentSpace
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x) :=
      ⟨h.toRiemannianMetric⟩
    ∃ d : MetricSpace M, ∃ ht : d.toUniformSpace.toTopologicalSpace = tM,
      letI : MetricSpace M := d.replaceTopology ht.symm
      BowenBasicSetCoding.HasOriginalRiemannianDistance
        (E := EuclideanSpace ℝ (Fin n)) (M := M) := by
  let : Bundle.RiemannianBundle
      (fun x : M => TangentSpace
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x) :=
    ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (fun x : M => TangentSpace
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x) :=
    ⟨h.inner, h.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M
  obtain ⟨d, ht, hd⟩ := MetricAdapter.exists_componentwise_length_metric h
  refine ⟨d, ht, ?_⟩
  let : MetricSpace M := d.replaceTopology ht.symm
  intro x y hy
  simpa only [MetricSpace.replaceTopology_eq, edist_dist] using hd x y hy


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
