import HolomorphicAnosov.Dynamics.Bowen.BowenBasicSetMarkovCoding

namespace HolomorphicAnosov

open Set

/-- Reindex an equal-symbol splice at an arbitrary integer seam. Both input
sequences and the resulting splice remain in the same invariant set. Source:
Manning Lemma 6, pp.427–428; Bowen Global Analysis I, Proposition (6.2). -/
theorem splice_at_integer
    {S : Type*} (L : Set (ℤ → S))
    (hshift : ∀ a ∈ L, ∀ k : ℤ, SymbolicDynamics.FullShift.shift k a ∈ L)
    (hsplice : ∀ a ∈ L, ∀ b ∈ L, a 0 = b 0 →
      ∃ c ∈ L, (∀ j : ℤ, j ≤ 0 → c j = a j) ∧
        (∀ j : ℤ, 0 ≤ j → c j = b j))
    (a : ℤ → S) (ha : a ∈ L) (b : ℤ → S) (hb : b ∈ L)
    (m : ℤ) (hab : a m = b 0) :
    ∃ c ∈ L, (∀ j : ℤ, j ≤ m → c j = a j) ∧
      (∀ j : ℤ, m ≤ j → c j = b (j - m)) := by
  have hzero : SymbolicDynamics.FullShift.shift m a 0 = b 0 := by
    simpa only [SymbolicDynamics.FullShift.shift_apply, add_zero] using hab
  obtain ⟨d, hd, hpast, hfuture⟩ :=
    hsplice _ (hshift a ha m) b hb hzero
  refine ⟨SymbolicDynamics.FullShift.shift (-m) d, hshift d hd (-m), ?_, ?_⟩
  · intro j hj
    simp only [SymbolicDynamics.FullShift.shift_apply]
    rw [hpast (-m + j) (by omega)]
    simp only [SymbolicDynamics.FullShift.shift_apply]
    congr 1
    omega
  · intro j hj
    simp only [SymbolicDynamics.FullShift.shift_apply]
    rw [hfuture (-m + j) (by omega)]
    congr 1
    omega

end HolomorphicAnosov
