import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PositiveComposition
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.CompositionInvariantFamilyEquiv
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.UniquePositiveBlockComposition
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.WeightedUniqueIndexCardSum
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.BoundedInvariantFamilySignedSum

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open scoped BigOperators Classical
noncomputable section

/-- The signed count of invariant fibre families indexed by all positive
compositions of size at most q is one. Each length-tagged family has exactly one
composition, namely its cardinality list. The fixed-composition equivalence
identifies each index fibre, and list lengths identify signs. Reindexing reduces
the result to the public signed family count. Source: Manning (1971), pp.218–219. -/
theorem composition_invariant_signed_sum {A : Type*} [Fintype A] [DecidableEq A]
    [Nonempty A] (g : A ≃ A) (q : ℕ) (hq : Fintype.card A ≤ q) :
    ∑ c : PositiveComposition q, (-1 : ℤ) ^ (c.2.length + 1) *
      Nat.card {S : Fin c.2.length → Finset A // (∀ k, (S k).Nonempty) ∧
        (∀ k, (S k).card = c.2.blocksFun k) ∧
        (Pairwise fun k j ↦ Disjoint (S k) (S j)) ∧ ∀ k, (S k).image g = S k} = 1 := by
  classical
  let p : PositiveComposition q → BoundedInvariantBlockFamily g q → Prop :=
    fun c U ↦ c.2.blocks = List.ofFn (fun i ↦ (U.2.val i).card)
  have huniq (U : BoundedInvariantBlockFamily g q) : ∃! c, p c U :=
    unique_positive_block_composition U.2.property.1 U.2.val
      U.2.property.2.1 U.2.property.2.2.1 hq
  have hsign (c : PositiveComposition q) (U : BoundedInvariantBlockFamily g q)
      (h : p c U) : (-1 : ℤ) ^ (c.2.length + 1) = (-1 : ℤ) ^ (U.1.val + 1) := by
    have hlen := congrArg List.length h
    simp only [List.length_ofFn] at hlen
    rw [show c.2.length = U.1.val from hlen]
  have h := weighted_unique_index_card_sum p huniq
    (fun c ↦ (-1 : ℤ) ^ (c.2.length + 1))
    (fun U ↦ (-1 : ℤ) ^ (U.1.val + 1)) hsign
  rw [bounded_invariant_family_signed_sum g q hq] at h
  apply Eq.trans (b := ∑ c : PositiveComposition q,
    (-1 : ℤ) ^ (c.2.length + 1) * Nat.card {U : BoundedInvariantBlockFamily g q // p c U}) ?_ h
  apply Finset.sum_congr rfl
  intro c _
  rw [Nat.card_congr (compositionInvariantFamilyEquiv g c)]

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
