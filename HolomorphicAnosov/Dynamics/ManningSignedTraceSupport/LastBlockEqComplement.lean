import Mathlib.Data.Finset.Lattice.Union
import Mathlib.Data.Fintype.Fin

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open scoped Classical
noncomputable section

/-- In a full ordered family of disjoint blocks, the last block is exactly the
complement of the preceding blocks. This proves the deletion inverse in
Manning's append-complement sign cancellation (1971), pp.218–219. Empty blocks
are allowed by this identity; the cancellation uses nonempty blocks separately. -/
theorem last_block_eq_complement {A : Type*} [Fintype A] [DecidableEq A] {k : ℕ}
    (S : Fin (k + 1) → Finset A)
    (hdis : Pairwise fun i j ↦ Disjoint (S i) (S j))
    (hcover : Finset.univ.biUnion S = Finset.univ) :
    S (Fin.last k) = Finset.univ \ Finset.univ.biUnion (fun i : Fin k ↦ S i.castSucc) := by
  classical
  ext a
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_biUnion,
    true_and, not_exists]
  constructor
  · intro ha i hi
    exact Finset.disjoint_left.mp (hdis (Fin.castSucc_ne_last i)) hi ha
  · intro ha
    have hm : a ∈ Finset.univ.biUnion S := by rw [hcover]; exact Finset.mem_univ a
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hm
    refine Fin.lastCases ?_ (fun j ↦ ?_) i hi
    · exact id
    · intro hj
      exact (ha j hj).elim

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
