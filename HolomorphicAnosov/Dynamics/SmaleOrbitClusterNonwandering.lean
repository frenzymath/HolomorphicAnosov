import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Dynamics.PeriodicPts.Defs

namespace HolomorphicAnosov
open Set Filter
open scoped Topology _root_.Topology

/-- A limit of a forward-orbit subsequence with strictly increasing indices is nonwandering (Shub,
Prop. 1.3). -/
theorem smale_nonwandering_of_tendsto_subseq
    {X : Type*} [TopologicalSpace X] (g : X → X) (x z : X)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hz : Tendsto (fun k : ℕ => g^[φ k] x) atTop (𝓝 z)) :
    ∀ U : Set X, IsOpen U → z ∈ U →
      ∃ k : ℕ, 0 < k ∧ (g^[k] '' U ∩ U).Nonempty := by
  intro U hU hzU
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hz (hU.mem_nhds hzU))
  have hlt : φ N < φ (N + 1) := hφ (Nat.lt_succ_self N)
  refine ⟨φ (N + 1) - φ N, Nat.sub_pos_of_lt hlt, g^[φ (N + 1)] x,
    ⟨g^[φ N] x, hN N le_rfl, ?_⟩, hN (N + 1) (Nat.le_succ N)⟩
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le]

end HolomorphicAnosov
