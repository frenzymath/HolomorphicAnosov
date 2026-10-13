import HolomorphicAnosov.Dynamics.Bowen.BowenBasicSetMarkovCoding
import HolomorphicAnosov.Dynamics.HirschPughHyperbolicSetFactOne
import HolomorphicAnosov.Topology.ExistsFullLengthMetric
import HolomorphicAnosov.Topology.EdistLtTopOfSameComponent
import Mathlib.Topology.EMetricSpace.Basic

namespace HolomorphicAnosov

open Set
open scoped Manifold ContDiff ENNReal Bundle

/-- A smooth positive original tensor supplies a full-length compatible metric
for the literal Bowen distance guard. Finite-distance classes are open, and each
connected component lies in one such class. -/
theorem original_tensor_exists_bowen_metric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [tM : TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    [FiniteDimensional ℝ E] [CompactSpace M] [T3Space M]
    (h : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
      ⟨h.toRiemannianMetric⟩
    ∃ d : MetricSpace M,
      ∃ ht : d.toUniformSpace.toTopologicalSpace = tM,
      letI : MetricSpace M := d.replaceTopology ht.symm
      BowenBasicSetCoding.HasOriginalRiemannianDistance (E := E) (M := M) := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨h.toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := by
    change letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
      ⟨h.toContinuousRiemannianMetric.toRiemannianMetric⟩
      IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)
    infer_instance
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) M
  have hfinite (x y : M) (hy : y ∈ connectedComponent x) :
      Manifold.riemannianEDist 𝓘(ℝ, E) x y < ⊤ :=
    edist_lt_top_of_same_component hy
  obtain ⟨d, ht, hd⟩ := exists_full_length_metric M
  refine ⟨d, ht, ?_⟩
  let : MetricSpace M := d.replaceTopology ht.symm
  intro x y hy
  rw [edist_dist]
  exact hd x y (hfinite x y hy)

end HolomorphicAnosov
