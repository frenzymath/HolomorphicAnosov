import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Dynamics.PeriodicPts.Defs
import HolomorphicAnosov.Dynamics.SmaleOrbitClusterNonwandering

namespace HolomorphicAnosov
open Set Filter
open scoped Topology _root_.Topology

/-- Every forward orbit in a compact metric space eventually lies in any open set containing the
nonwandering set (Shub, Cor. 1.4). -/
theorem smale_eventually_mem_of_nonwandering_subset
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (g : X → X) (x : X) {U : Set X} (hU : IsOpen U)
    (hΩU : {z | ∀ V : Set X, IsOpen V → z ∈ V →
      ∃ k : ℕ, 0 < k ∧ (g^[k] '' V ∩ V).Nonempty} ⊆ U) :
    ∀ᶠ k : ℕ in atTop, g^[k] x ∈ U := by
  by_contra h
  have hfreq : ∃ᶠ k : ℕ in atTop, g^[k] x ∈ Uᶜ := by
    simpa only [Filter.Frequently, Set.mem_compl_iff, not_not] using h
  obtain ⟨z, hzU, φ, hφ, hz⟩ := hU.isClosed_compl.isCompact.tendsto_subseq' hfreq
  exact hzU (hΩU (smale_nonwandering_of_tendsto_subseq g x z φ hφ hz))

end HolomorphicAnosov
