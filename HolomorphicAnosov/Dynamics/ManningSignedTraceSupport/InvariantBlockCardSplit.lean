import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.SetTheory.Cardinal.Finite

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open scoped Classical
noncomputable section

/-- Every ordered invariant disjoint nonempty block family is either full or
proper, and these two alternatives split its finite cardinality. Filter the
finite function space by the block conditions, then partition by full coverage.
Source: Manning (1971), pp.218–219, complement cancellation. -/
theorem invariant_block_card_split {A : Type*} [Fintype A] [DecidableEq A]
    (g : A ≃ A) (k : ℕ) :
    Nat.card {S : Fin k → Finset A // (∀ i, (S i).Nonempty) ∧
      (Pairwise fun i j ↦ Disjoint (S i) (S j)) ∧ (∀ i, (S i).image g = S i)} =
    Nat.card {S : Fin k → Finset A // (∀ i, (S i).Nonempty) ∧
      (Pairwise fun i j ↦ Disjoint (S i) (S j)) ∧
      (∀ i, (S i).image g = S i) ∧ Finset.univ.biUnion S = Finset.univ} +
    Nat.card {S : Fin k → Finset A // (∀ i, (S i).Nonempty) ∧
      (Pairwise fun i j ↦ Disjoint (S i) (S j)) ∧
      (∀ i, (S i).image g = S i) ∧ Finset.univ.biUnion S ≠ Finset.univ} := by
  classical
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun S : Fin k → Finset A ↦
      (∀ i, (S i).Nonempty) ∧ (Pairwise fun i j ↦ Disjoint (S i) (S j)) ∧
        (∀ i, (S i).image g = S i)))
    (p := fun S ↦ Finset.univ.biUnion S = Finset.univ)
  simpa only [Finset.filter_filter, and_assoc] using h.symm

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
