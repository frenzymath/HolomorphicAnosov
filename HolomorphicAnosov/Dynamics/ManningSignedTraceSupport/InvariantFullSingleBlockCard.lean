import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.InvariantBlockCompletionEquiv
import Mathlib.SetTheory.Cardinal.Finite

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open scoped Classical
noncomputable section

/-- On a nonempty finite alphabet, exactly one invariant full single-block
family exists: the block containing every label. Via complement completion it
corresponds to the unique empty family. This is the surviving lower boundary
in Manning's signed cancellation (1971), pp.218–219. -/
theorem invariant_full_single_block_card {A : Type*} [Fintype A] [DecidableEq A]
    [Nonempty A] (g : A ≃ A) :
    Nat.card {T : Fin 1 → Finset A // (∀ i, (T i).Nonempty) ∧
      (Pairwise fun i j ↦ Disjoint (T i) (T j)) ∧
      (∀ i, (T i).image g = T i) ∧ Finset.univ.biUnion T = Finset.univ} = 1 := by
  classical
  rw [← Nat.card_congr (invariantBlockCompletionEquiv g 0)]
  let Z := {S : Fin 0 → Finset A // (∀ i, (S i).Nonempty) ∧
    (Pairwise fun i j ↦ Disjoint (S i) (S j)) ∧
    (∀ i, (S i).image g = S i) ∧ Finset.univ.biUnion S ≠ Finset.univ}
  let z : Z := ⟨Fin.elim0, by
    simp only [IsEmpty.forall_iff, Pairwise, Finset.univ_eq_empty,
      Finset.biUnion_empty, true_and]
    exact (Finset.univ_nonempty : (Finset.univ : Finset A).Nonempty).ne_empty.symm⟩
  let : Unique Z := ⟨⟨z⟩, fun S ↦ Subtype.ext (funext fun i ↦ Fin.elim0 i)⟩
  exact Nat.card_unique

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
