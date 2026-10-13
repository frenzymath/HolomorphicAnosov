import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.BlockMatching

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open Set
open scoped Classical
noncomputable section

/-- Two legal matchings from the same block have identical target blocks when
legal successors are unique among their target labels. Compare the two images
of each source label, then use surjectivity of both matching equivalences.
This elementary finite matching fact is used in Manning (1971), pp.218–219. -/
theorem blockMatching_targets_eq {N : ℕ} (T : Matrix (Fin N) (Fin N) ℤ)
    {s t u : Finset (Fin N)} (ht : BlockMatching T s t) (hu : BlockMatching T s u)
    (hunique : ∀ i ∈ s, ∀ j ∈ t, ∀ k ∈ u, T i j = 1 → T i k = 1 → j = k) :
    t = u := by
  obtain ⟨a, ha⟩ := ht
  obtain ⟨b, hb⟩ := hu
  have hab : ∀ i : ↥s, (a i).val = (b i).val :=
    fun i ↦ hunique i.val i.property (a i).val (a i).property (b i).val (b i).property
      (ha i) (hb i)
  apply Finset.ext
  intro i
  constructor
  · intro hi
    obtain ⟨v, hv⟩ := a.surjective ⟨i, hi⟩
    have hh := hab v
    rw [hv] at hh
    simpa only [← hh] using (b v).property
  · intro hi
    obtain ⟨v, hv⟩ := b.surjective ⟨i, hi⟩
    have hh := hab v
    rw [hv] at hh
    simpa only [hh] using (a v).property

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
