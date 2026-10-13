import Mathlib.Data.List.Count

universe u v
namespace HolomorphicAnosov.Topology

/-- In a finite balanced list of directed edges, a nonloop edge has an outgoing
successor among the other occurrences.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 proof p.167. At the selected
edge's target, the total incoming count is positive. Balance makes the outgoing
count positive; since the selected edge is not a loop, it does not contribute
to that outgoing count, so another occurrence supplies a successor. -/
theorem list_endpoint_balance_successor {E : Type u} {V : Type v} [DecidableEq V]
    (s t : E → V) (e : E) (l : List E) (hne : s e ≠ t e)
    (hb : ∀ v, ((e :: l).map s).count v = ((e :: l).map t).count v) :
    ∃ f ∈ l, s f = t e := by
  have h := hb (t e)
  simp [hne] at h
  have hp : 0 < (l.map s).count (t e) := by omega
  obtain ⟨f, hf, he⟩ := List.mem_map.mp (List.count_pos_iff.mp hp)
  exact ⟨f, hf, he⟩
end HolomorphicAnosov.Topology
