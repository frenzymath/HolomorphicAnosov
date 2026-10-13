import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.LastBlockEqComplement
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.InvariantComplementSignPair

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open scoped Classical
noncomputable section

/-- Delete the last block of a full nonempty disjoint invariant family. The
remaining union is proper, because a label in the deleted block cannot occur
in any remaining block. The last block is exactly the complement, so appending
it recovers the full family with the opposite sign. The counting application
requires a nonempty prefix to exclude the sole surviving full one-block family.
Source: Manning (1971), pp.218–219. -/
theorem invariant_block_deletion {A : Type*} [Fintype A] [DecidableEq A]
    (g : A ≃ A) {k : ℕ} (S : Fin (k + 1) → Finset A)
    (hne : ∀ i, (S i).Nonempty)
    (hdis : Pairwise fun i j ↦ Disjoint (S i) (S j))
    (hinv : ∀ i, (S i).image g = S i)
    (hcover : Finset.univ.biUnion S = Finset.univ) :
    let P : Fin k → Finset A := fun i ↦ S i.castSucc
    (∀ i, (P i).Nonempty) ∧
    (Pairwise fun i j ↦ Disjoint (P i) (P j)) ∧
    (∀ i, (P i).image g = P i) ∧
    Finset.univ.biUnion P ≠ Finset.univ ∧
    S (Fin.last k) = Finset.univ \ Finset.univ.biUnion P ∧
    (-1 : ℤ) ^ (k + 1) + (-1 : ℤ) ^ (k + 2) = 0 := by
  classical
  dsimp only
  have hp : Finset.univ.biUnion (fun i : Fin k ↦ S i.castSucc) ≠ Finset.univ := by
    intro heq
    obtain ⟨a, ha⟩ := hne (Fin.last k)
    have hm : a ∈ Finset.univ.biUnion (fun i : Fin k ↦ S i.castSucc) := by
      rw [heq]; exact Finset.mem_univ a
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hm
    exact Finset.disjoint_left.mp (hdis (Fin.castSucc_ne_last i)) hi ha
  refine ⟨fun i ↦ hne i.castSucc, ?_, fun i ↦ hinv i.castSucc, hp,
    last_block_eq_complement S hdis hcover, ?_⟩
  · intro i j hij
    exact hdis (fun h ↦ hij (Fin.castSucc_injective _ h))
  · exact (invariant_complement_sign_pair g (fun i : Fin k ↦ S i.castSucc)
      (fun i ↦ hinv i.castSucc) hp).2.2.2

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
