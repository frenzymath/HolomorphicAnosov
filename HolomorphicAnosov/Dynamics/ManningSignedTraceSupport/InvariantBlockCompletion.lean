import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.InvariantComplementSignPair
import Mathlib.Data.Fin.VecNotation

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open scoped Classical
noncomputable section

/-- Append the complement to a proper nonempty family of disjoint invariant
blocks. The result is a full family of nonempty disjoint invariant blocks, and
its alternating sign is opposite to that of the original family. This is the
forward pairing operation of Manning (1971), pp.218–219. -/
theorem invariant_block_completion {A : Type*} [Fintype A] [DecidableEq A]
    (g : A ≃ A) {k : ℕ} (S : Fin k → Finset A)
    (hne : ∀ i, (S i).Nonempty)
    (hdis : Pairwise fun i j ↦ Disjoint (S i) (S j))
    (hinv : ∀ i, (S i).image g = S i)
    (hproper : Finset.univ.biUnion S ≠ Finset.univ) :
    let C := (Finset.univ : Finset A) \ Finset.univ.biUnion S
    let T : Fin (k + 1) → Finset A := Fin.snoc S C
    (∀ i, (T i).Nonempty) ∧
    (Pairwise fun i j ↦ Disjoint (T i) (T j)) ∧
    (∀ i, (T i).image g = T i) ∧
    Finset.univ.biUnion T = Finset.univ ∧
    (-1 : ℤ) ^ (k + 1) + (-1 : ℤ) ^ (k + 2) = 0 := by
  classical
  obtain ⟨hCne, hCdis, hCinv, hsign⟩ := invariant_complement_sign_pair g S hinv hproper
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, hsign⟩
  · intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa only [Fin.snoc_last] using hCne
    · simpa only [Fin.snoc_castSucc] using hne j
  · intro i j hij
    revert j
    refine Fin.lastCases ?_ (fun i ↦ ?_) i
    · intro j hij
      refine Fin.lastCases ?_ (fun j ↦ ?_) j hij
      · exact fun h ↦ (h rfl).elim
      · intro _
        simpa only [Fin.snoc_last, Fin.snoc_castSucc] using (hCdis j).symm
    · intro j hij
      refine Fin.lastCases ?_ (fun j ↦ ?_) j hij
      · intro _
        simpa only [Fin.snoc_last, Fin.snoc_castSucc] using hCdis i
      · intro h
        simpa only [Fin.snoc_castSucc] using hdis (fun heq ↦ h (congrArg Fin.castSucc heq))
  · intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa only [Fin.snoc_last] using hCinv
    · simpa only [Fin.snoc_castSucc] using hinv j
  · apply Finset.eq_univ_of_forall
    intro a
    by_cases ha : a ∈ Finset.univ.biUnion S
    · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp ha
      exact Finset.mem_biUnion.mpr ⟨i.castSucc, Finset.mem_univ _, by simpa using hi⟩
    · exact Finset.mem_biUnion.mpr ⟨Fin.last k, Finset.mem_univ _, by simpa using ha⟩

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
