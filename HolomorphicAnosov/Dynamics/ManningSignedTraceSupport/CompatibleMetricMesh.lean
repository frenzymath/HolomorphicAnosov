import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.CompatibleMetricModulus
import Mathlib.Topology.MetricSpace.Bounded

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter

open Set Filter _root_.Topology
open scoped BigOperators ENNReal Classical
noncomputable section

/-- Use the compact identity modulus at half the desired diameter. Every pair in
a new-metric small set has old distance below that half bound. The old diameter
is at most the half bound, leaving the required strict final margin. -/
theorem compatible_metric_mesh {X : Type*} [old : MetricSpace X] [CompactSpace X]
    (new : MetricSpace X)
    (ht : new.toUniformSpace.toTopologicalSpace = old.toUniformSpace.toTopologicalSpace)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s : Set X, @Metric.diam X new.toPseudoMetricSpace s < δ →
      @Metric.diam X old.toPseudoMetricSpace s < ε := by
  obtain ⟨δ, hδ, hmod⟩ := @compatible_metric_modulus X old (inferInstance : @CompactSpace X old.toUniformSpace.toTopologicalSpace) new ht (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro s hs
  have hc : @CompactSpace X new.toUniformSpace.toTopologicalSpace := ht.symm ▸
    (inferInstance : @CompactSpace X old.toUniformSpace.toTopologicalSpace)
  have hb : @Bornology.IsBounded X new.toBornology s :=
    @Metric.isBounded_of_compactSpace X s new.toPseudoMetricSpace hc
  have hpair : ∀ x ∈ s, ∀ y ∈ s, old.dist x y ≤ ε / 2 := by
    intro x hx y hy
    exact (hmod x y ((@Metric.dist_le_diam_of_mem X s x y
      new.toPseudoMetricSpace hb hx hy).trans_lt hs)).le
  exact (@Metric.diam_le_of_forall_dist_le X s old.toPseudoMetricSpace (ε / 2) (half_pos hε).le hpair).trans_lt
    (half_lt_self hε)


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter
