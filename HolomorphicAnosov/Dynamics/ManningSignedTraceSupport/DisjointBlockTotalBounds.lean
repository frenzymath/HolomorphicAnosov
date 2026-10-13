import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open scoped BigOperators Classical

/-- The sum of cardinalities of a nonempty ordered family of nonempty disjoint
blocks is positive and at most the finite alphabet cardinality. Disjointness
identifies the sum with the union cardinality, and one block supplies a label
in that union. This is the range of composition sizes in Manning (1971), pp.217–219. -/
theorem disjoint_block_total_bounds {A : Type*} [Fintype A] {k : ℕ} (hk : 0 < k)
    (S : Fin k → Finset A) (hne : ∀ i, (S i).Nonempty)
    (hdis : Pairwise fun i j ↦ Disjoint (S i) (S j)) :
    0 < ∑ i, (S i).card ∧ ∑ i, (S i).card ≤ Fintype.card A := by
  classical
  have hu : (Finset.univ.biUnion S).card = ∑ i, (S i).card :=
    Finset.card_biUnion (fun i _ j _ hij ↦ hdis hij)
  rw [← hu]
  constructor
  · apply Finset.card_pos.mpr
    obtain ⟨a, ha⟩ := hne ⟨0, hk⟩
    exact ⟨a, Finset.mem_biUnion.mpr ⟨⟨0, hk⟩, Finset.mem_univ _, ha⟩⟩
  · exact Finset.card_le_univ _

end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
