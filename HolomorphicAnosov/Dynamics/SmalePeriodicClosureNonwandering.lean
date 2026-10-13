import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Dynamics.PeriodicPts.Defs
import HolomorphicAnosov.Dynamics.SmaleNonwanderingClosed

namespace HolomorphicAnosov
open Set Filter
open scoped Topology _root_.Topology

/-- The closure of the periodic points is contained in the nonwandering set (Shub, p. 2). -/
theorem smale_closure_periodicPts_subset_nonwandering
    {X : Type*} [TopologicalSpace X] (g : X → X) :
    closure (Function.periodicPts g) ⊆
      {x | ∀ U : Set X, IsOpen U → x ∈ U →
        ∃ k : ℕ, 0 < k ∧ (g^[k] '' U ∩ U).Nonempty} := by
  apply closure_minimal ?_ (smale_isClosed_nonwandering g)
  intro x hx U _ hxU
  obtain ⟨k, hk, hfix⟩ := Function.mem_periodicPts.mp hx
  exact ⟨k, hk, x, ⟨x, hxU, hfix⟩, hxU⟩

end HolomorphicAnosov
