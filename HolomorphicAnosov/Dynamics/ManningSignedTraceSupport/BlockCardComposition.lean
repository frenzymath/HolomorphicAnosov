import Mathlib.Combinatorics.Enumerative.Composition

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open scoped BigOperators

/-- The composition associated with the cardinalities of an ordered nonempty
block family. Its total is the sum of the block cardinalities and its list is
literally those cardinalities in their original order. Source: Manning (1971),
pp.217–219, compositions indexing ordered block families. -/
def blockCardComposition {A : Type*} {k : ℕ} (S : Fin k → Finset A)
    (hne : ∀ i, (S i).Nonempty) : Composition (∑ i, (S i).card) where
  blocks := List.ofFn (fun i ↦ (S i).card)
  blocks_pos := by
    intro n hn
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hn
    exact (hne i).card_pos
  blocks_sum := List.sum_ofFn

end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
