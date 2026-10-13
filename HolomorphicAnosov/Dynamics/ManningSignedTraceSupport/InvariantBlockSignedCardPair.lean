import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.InvariantBlockCompletionEquiv
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Ring

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open scoped Classical
noncomputable section

/-- The signed cardinal contributions of proper k-block invariant families and
full (k+1)-block invariant families cancel exactly. Their public complement
completion equivalence identifies cardinalities, and the signs differ by one
power of minus one. This is the local finite cancellation in Manning (1971),
pp.218–219, before identifying these families with periodic tuple words. -/
theorem invariant_block_signed_card_pair {A : Type*} [Fintype A] [DecidableEq A]
    (g : A ≃ A) (k : ℕ) :
    (-1 : ℤ) ^ (k + 1) * Nat.card
      {S : Fin k → Finset A // (∀ i, (S i).Nonempty) ∧
        (Pairwise fun i j ↦ Disjoint (S i) (S j)) ∧
        (∀ i, (S i).image g = S i) ∧ Finset.univ.biUnion S ≠ Finset.univ} +
    (-1 : ℤ) ^ (k + 2) * Nat.card
      {T : Fin (k + 1) → Finset A // (∀ i, (T i).Nonempty) ∧
        (Pairwise fun i j ↦ Disjoint (T i) (T j)) ∧
        (∀ i, (T i).image g = T i) ∧ Finset.univ.biUnion T = Finset.univ} = 0 := by
  rw [Nat.card_congr (invariantBlockCompletionEquiv g k)]
  rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
  ring

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
