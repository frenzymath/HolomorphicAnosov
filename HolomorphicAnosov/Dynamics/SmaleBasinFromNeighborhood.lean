import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Dynamics.PeriodicPts.Defs
import HolomorphicAnosov.Dynamics.SmaleOrbitClusterNonwandering
import HolomorphicAnosov.Dynamics.SmaleDistanceFromClusterLimits

namespace HolomorphicAnosov
open Set Filter
open scoped Topology _root_.Topology

/-- Convert the captured neighborhood label into actual basin membership.
Source: Shub, Lemma 2.2, printed p.9. A late orbit in U has all subsequence
limits in closure U, and every such limit is nonwandering. The neighborhood
separation guard therefore puts these limits in the chosen component A. -/
theorem smale_basin_of_eventually_mem_neighborhood
    {X : Type*} [MetricSpace X] [CompactSpace X] (g : X → X) (x : X)
    (A U : Set X)
    (hguard : {z | ∀ V : Set X, IsOpen V → z ∈ V →
      ∃ k : ℕ, 0 < k ∧ (g^[k] '' V ∩ V).Nonempty} ∩ closure U ⊆ A)
    (htail : ∀ᶠ n : ℕ in atTop, g^[n] x ∈ U) :
    Tendsto (fun k : ℕ ↦ Metric.infDist (g^[k] x) A) atTop (𝓝 0) := by
  apply smale_infDist_tendsto_of_subsequence_limits g x A
  intro z φ hφ hz
  apply hguard
  refine ⟨smale_nonwandering_of_tendsto_subseq g x z φ hφ hz, ?_⟩
  apply isClosed_closure.mem_of_tendsto hz
  filter_upwards [hφ.tendsto_atTop.eventually htail] with k hk
  exact subset_closure hk

end HolomorphicAnosov
