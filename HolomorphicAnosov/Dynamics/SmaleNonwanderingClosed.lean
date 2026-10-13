import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Dynamics.PeriodicPts.Defs

namespace HolomorphicAnosov
open Set Filter
open scoped Topology _root_.Topology

/-- The nonwandering set of a self-map is closed (Shub, Prop. 1.1). -/
theorem smale_isClosed_nonwandering {X : Type*} [TopologicalSpace X] (g : X → X) :
    IsClosed {x | ∀ U : Set X, IsOpen U → x ∈ U →
      ∃ k : ℕ, 0 < k ∧ (g^[k] '' U ∩ U).Nonempty} := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  change ¬ (∀ U : Set X, IsOpen U → x ∈ U →
    ∃ k : ℕ, 0 < k ∧ (g^[k] '' U ∩ U).Nonempty) at hx
  push Not at hx
  obtain ⟨U, hU, hxU, hreturn⟩ := hx
  refine ⟨U, ?_, hU, hxU⟩
  intro y hy hynw
  obtain ⟨k, hk, hhit⟩ := hynw U hU hy
  exact hhit.ne_empty (hreturn k hk)

end HolomorphicAnosov
