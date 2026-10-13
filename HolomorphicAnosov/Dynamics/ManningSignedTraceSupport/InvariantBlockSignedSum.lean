import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.InvariantBlockCompletionEquiv
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.InvariantBlockCardSplit
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.InvariantBlockSignedCardPair
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.InvariantFullSingleBlockCard
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.DisjointNonemptyBlocksLengthLt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open scoped BigOperators Classical
noncomputable section

/-- For a permutation of a nonempty finite alphabet, the signed number of all
ordered families of nonempty disjoint invariant blocks, with lengths from one
to any bound at least the alphabet cardinality, is one. Split full from proper
families, cancel full(k+1)-block families against proper k-block families, and
telescope. The empty proper family contributes the initial one, while proper
families at the upper bound are impossible. Source: Manning (1971), pp.218–219. -/
theorem invariant_block_signed_sum {A : Type*} [Fintype A] [DecidableEq A]
    [Nonempty A] (g : A ≃ A) (q : ℕ) (hq : Fintype.card A ≤ q) :
    ∑ k ∈ Finset.range q, (-1 : ℤ) ^ (k + 2) *
      Nat.card {S : Fin (k + 1) → Finset A // (∀ i, (S i).Nonempty) ∧
        (Pairwise fun i j ↦ Disjoint (S i) (S j)) ∧
        (∀ i, (S i).image g = S i)} = 1 := by
  classical
  let U (k : ℕ) : ℤ := Nat.card {S : Fin k → Finset A // (∀ i, (S i).Nonempty) ∧
    (Pairwise fun i j ↦ Disjoint (S i) (S j)) ∧ (∀ i, (S i).image g = S i)}
  let P (k : ℕ) : ℤ := Nat.card {S : Fin k → Finset A // (∀ i, (S i).Nonempty) ∧
    (Pairwise fun i j ↦ Disjoint (S i) (S j)) ∧
    (∀ i, (S i).image g = S i) ∧ Finset.univ.biUnion S ≠ Finset.univ}
  let F (k : ℕ) : ℤ := Nat.card {S : Fin k → Finset A // (∀ i, (S i).Nonempty) ∧
    (Pairwise fun i j ↦ Disjoint (S i) (S j)) ∧
    (∀ i, (S i).image g = S i) ∧ Finset.univ.biUnion S = Finset.univ}
  have hterm (k : ℕ) : (-1 : ℤ) ^ (k + 2) * U (k + 1) =
      (-1 : ℤ) ^ (k + 2) * P (k + 1) - (-1 : ℤ) ^ (k + 1) * P k := by
    have hsplit : U (k + 1) = F (k + 1) + P (k + 1) := by
      dsimp [U, F, P]
      exact_mod_cast invariant_block_card_split g (k + 1)
    have hpair : (-1 : ℤ) ^ (k + 1) * P k +
        (-1 : ℤ) ^ (k + 2) * F (k + 1) = 0 := invariant_block_signed_card_pair g k
    rw [hsplit, mul_add]
    linarith
  have hp0 : P 0 = 1 := by
    dsimp [P]
    rw [Nat.card_congr (invariantBlockCompletionEquiv g 0), invariant_full_single_block_card g]
    rfl
  have hpq : P q = 0 := by
    let : IsEmpty {S : Fin q → Finset A // (∀ i, (S i).Nonempty) ∧
      (Pairwise fun i j ↦ Disjoint (S i) (S j)) ∧
      (∀ i, (S i).image g = S i) ∧ Finset.univ.biUnion S ≠ Finset.univ} :=
      ⟨fun S ↦ (Nat.not_lt_of_ge hq)
        (disjoint_nonempty_blocks_length_lt S.val S.property.1 S.property.2.1
          S.property.2.2.2)⟩
    simp [P]
  change ∑ k ∈ Finset.range q, (-1 : ℤ) ^ (k + 2) * U (k + 1) = 1
  simp_rw [hterm]
  have htel := Finset.sum_range_sub (fun k ↦ (-1 : ℤ) ^ (k + 1) * P k) q
  simpa only [Nat.add_assoc, hpq, hp0, mul_zero, pow_one, mul_one, sub_neg_eq_add,
    zero_add] using htel

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
