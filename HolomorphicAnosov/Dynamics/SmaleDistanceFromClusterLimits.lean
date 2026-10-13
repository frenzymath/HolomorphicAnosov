import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Dynamics.PeriodicPts.Defs

namespace HolomorphicAnosov
open Set Filter
open scoped Topology _root_.Topology

/-- If every limit of a forward-orbit subsequence lies in a fixed set in a compact metric space, the
orbit's infimum distance to that set tends to zero (Shub, Lemma 2.2). -/
theorem smale_infDist_tendsto_of_subsequence_limits
    {X : Type*} [MetricSpace X] [CompactSpace X] (g : X → X) (x : X) (A : Set X)
    (hcluster : ∀ (z : X) (φ : ℕ → ℕ), StrictMono φ →
      Tendsto (fun k : ℕ ↦ g^[φ k] x) atTop (𝓝 z) → z ∈ A) :
    Tendsto (fun k : ℕ ↦ Metric.infDist (g^[k] x) A) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsmall : ∀ᶠ k : ℕ in atTop, Metric.infDist (g^[k] x) A < ε := by
    by_contra h
    have hfreq : ∃ᶠ k : ℕ in atTop, g^[k] x ∈ {z | ε ≤ Metric.infDist z A} := by
      simpa only [Filter.Frequently, Set.mem_ofPred_eq, not_le] using h
    have hclosed : IsClosed {z : X | ε ≤ Metric.infDist z A} :=
      isClosed_le continuous_const (Metric.continuous_infDist_pt A)
    obtain ⟨z, hz, φ, hφ, hlim⟩ := hclosed.isCompact.tendsto_subseq' hfreq
    have hzA := hcluster z φ hφ hlim
    have hzero := Metric.infDist_zero_of_mem hzA
    exact (not_le_of_gt hε) (hzero ▸ hz)
  filter_upwards [hsmall] with k hk
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg Metric.infDist_nonneg] using hk

end HolomorphicAnosov
