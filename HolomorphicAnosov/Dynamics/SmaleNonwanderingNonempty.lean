import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Dynamics.PeriodicPts.Defs
import HolomorphicAnosov.Dynamics.SmaleOrbitClusterNonwandering

namespace HolomorphicAnosov
open Set Filter
open scoped Topology _root_.Topology

/-- The nonwandering set of a self-map of a nonempty compact metric space is nonempty (Shub, Prop.
1.3). -/
theorem smale_nonwandering_nonempty {X : Type*} [MetricSpace X] [CompactSpace X]
    [Nonempty X] (g : X → X) :
    {x | ∀ U : Set X, IsOpen U → x ∈ U →
      ∃ k : ℕ, 0 < k ∧ (g^[k] '' U ∩ U).Nonempty}.Nonempty := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨z, φ, hφ, hz⟩ := CompactSpace.tendsto_subseq (fun k : ℕ => g^[k] x)
  exact ⟨z, smale_nonwandering_of_tendsto_subseq g x z φ hφ hz⟩

end HolomorphicAnosov
