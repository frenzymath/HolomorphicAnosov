import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.InvariantBlockCompletion
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.InvariantBlockDeletion

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open scoped Classical
noncomputable section

/-- Appending the invariant complement and deleting the final block are inverse
bijections between proper k-block families and full (k+1)-block families.
Every block is nonempty, blocks are disjoint, and the permutation preserves each
block. For k=0 this pairs the empty family with the full single block; the signed
count restricts to k≥1, leaving that single full block as the survivor.
Source: Manning (1971), pp.218–219. -/
def invariantBlockCompletionEquiv {A : Type*} [Fintype A] [DecidableEq A]
    (g : A ≃ A) (k : ℕ) :
    {S : Fin k → Finset A // (∀ i, (S i).Nonempty) ∧
      (Pairwise fun i j ↦ Disjoint (S i) (S j)) ∧
      (∀ i, (S i).image g = S i) ∧ Finset.univ.biUnion S ≠ Finset.univ} ≃
    {T : Fin (k + 1) → Finset A // (∀ i, (T i).Nonempty) ∧
      (Pairwise fun i j ↦ Disjoint (T i) (T j)) ∧
      (∀ i, (T i).image g = T i) ∧ Finset.univ.biUnion T = Finset.univ} where
  toFun S := ⟨Fin.snoc S.val (Finset.univ \ Finset.univ.biUnion S.val), by
    have h := invariant_block_completion g S.val S.property.1 S.property.2.1
      S.property.2.2.1 S.property.2.2.2
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩⟩
  invFun T := ⟨fun i ↦ T.val i.castSucc, by
    have h := invariant_block_deletion g T.val T.property.1 T.property.2.1
      T.property.2.2.1 T.property.2.2.2
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩⟩
  left_inv S := by
    apply Subtype.ext
    funext i
    change Fin.snoc (α := fun _ ↦ Finset A) S.val (Finset.univ \ Finset.univ.biUnion S.val) i.castSucc = S.val i
    simp only [Fin.snoc_castSucc]
  right_inv T := by
    apply Subtype.ext
    funext i
    change Fin.snoc (α := fun _ ↦ Finset A) (fun j : Fin k ↦ T.val j.castSucc)
      (Finset.univ \ Finset.univ.biUnion (fun j : Fin k ↦ T.val j.castSucc)) i = T.val i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [Fin.snoc_last]
      exact (last_block_eq_complement T.val T.property.2.1 T.property.2.2.2).symm
    · simp only [Fin.snoc_castSucc]

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
