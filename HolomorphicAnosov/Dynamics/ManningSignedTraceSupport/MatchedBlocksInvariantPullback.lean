import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.MatchedBlocksPullbackConstant

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open scoped Classical
noncomputable section

/-- If a matched label block returns after m steps and the coordinate maps
intertwine that return with a fibre permutation, its pullback is invariant
under the permutation. Constancy identifies membership at time zero and time m;
the intertwining identity identifies the latter with membership after applying
the permutation. This is the forward periodic-word/block correspondence of
Manning (1971), pp.218–219, without any assertion that the permutation is identity. -/
theorem matched_blocks_invariant_pullback {A : Type*} [Fintype A] {N : ℕ}
    (T : Matrix (Fin N) (Fin N) ℤ) (l : ℤ → A → Fin N)
    (hforced : ∀ j a b, T (l j a) (l (j + 1) b) = 1 → a = b)
    (S : ℤ → Finset (Fin N))
    (hs : ∀ j i, i ∈ S j → ∃ a, l j a = i)
    (hmatch : ∀ j, BlockMatching T (S j) (S (j + 1)))
    (g : A ≃ A) (m : ℤ) (hperiod : S m = S 0)
    (hreturn : ∀ a, l m a = l 0 (g a)) :
    (Finset.univ.filter (fun a ↦ l 0 a ∈ S 0)).image g =
      Finset.univ.filter (fun a ↦ l 0 a ∈ S 0) := by
  classical
  have hconst := matched_blocks_pullback_constant T l hforced S hs hmatch m
  have hmem (a : A) : l 0 (g a) ∈ S 0 ↔ l 0 a ∈ S 0 := by
    have h := Finset.ext_iff.mp hconst a
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, hperiod, hreturn] using h
  ext a
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact (hmem b).mpr hb
  · intro ha
    exact ⟨g.symm a, (hmem (g.symm a)).mp (by simpa using ha), g.apply_symm_apply a⟩

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
