import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic.Linarith

/-! # Bounded open connected subsets of the real line
Source context: the first-exit chord construction in Cairns (1951), §3,
pp.861–862. The explicit interval argument is agent-written.
-/
namespace HolomorphicAnosov
open Set
open scoped _root_.Topology

/-- A nonempty bounded open connected real set is the interval between its
infimum and supremum, and both endpoints belong to its closure. Source context:
Cairns (1951), §3, pp.861–862; expanded first-exit argument.

Openness supplies points on both sides of each member, so the infimum and
supremum strictly bound every member. Connectedness fills the open interval
between them. Nonemptiness then makes the endpoints distinct, and the standard
infimum/supremum closure property puts them in the closure. -/
theorem bounded_open_connected_real_interval {s : Set ℝ}
    (hs : IsOpen s) (hc : IsConnected s) (hb : Bornology.IsBounded s) :
    ∃ u v : ℝ, u < v ∧ s = Ioo u v ∧ u ∈ closure s ∧ v ∈ closure s := by
  have hstrict : ∀ x ∈ s, sInf s < x ∧ x < sSup s := by
    intro x hx
    obtain ⟨l, r, ⟨hl, hr⟩, hsub⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp (hs.mem_nhds hx)
    have hleft : (l + x) / 2 ∈ s := hsub (by constructor <;> linarith)
    have hright : (x + r) / 2 ∈ s := hsub (by constructor <;> linarith)
    constructor
    · exact lt_of_le_of_lt (csInf_le hb.bddBelow hleft) (by linarith)
    · exact lt_of_lt_of_le (by linarith : x < (x + r) / 2) (le_csSup hb.bddAbove hright)
  obtain ⟨x, hx⟩ := hc.nonempty
  refine ⟨sInf s, sSup s, (hstrict x hx).1.trans (hstrict x hx).2, ?_,
    csInf_mem_closure hc.nonempty hb.bddBelow, csSup_mem_closure hc.nonempty hb.bddAbove⟩
  exact Subset.antisymm hstrict (hc.Ioo_csInf_csSup_subset hb.bddBelow hb.bddAbove)

end HolomorphicAnosov
