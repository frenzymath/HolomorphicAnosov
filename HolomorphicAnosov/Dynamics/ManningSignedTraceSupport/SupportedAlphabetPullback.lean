import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.Alphabet

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open Set
open scoped Classical
noncomputable section

/-- Pulling the blocks of a supported alphabet through an injective coordinate
map preserves nonemptiness, prescribed cardinalities and disjointness, and taking
the coordinate images recovers the original blocks. Every supported label has
a preimage, so each image of a pullback is exact. Source: Manning (1971),
pp.218–219, fibre block reconstruction. -/
theorem supported_alphabet_pullback {A X : Type*} [Fintype A] {N r : ℕ}
    (R : Fin N → Set X) (c : Composition r) (l : A → Fin N)
    (hl : Function.Injective l) (x : X)
    (hlabel : ∀ i, x ∈ R i → ∃ a, l a = i) (s : Alphabet R c)
    (hs : ∀ k i, i ∈ s.val k → x ∈ R i) :
    let S : Fin c.length → Finset A := fun k ↦ Finset.univ.filter (fun a ↦ l a ∈ s.val k)
    (∀ k, (S k).Nonempty) ∧ (∀ k, (S k).card = c.blocksFun k) ∧
      (Pairwise fun k j ↦ Disjoint (S k) (S j)) ∧ ∀ k, (S k).image l = s.val k := by
  classical
  dsimp only
  have himage (k : Fin c.length) :
      (Finset.univ.filter (fun a ↦ l a ∈ s.val k)).image l = s.val k := by
    ext i
    constructor
    · intro hi
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
      exact (Finset.mem_filter.mp ha).2
    · intro hi
      obtain ⟨a, ha⟩ := hlabel i (hs k i hi)
      exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ha.symm ▸ hi⟩, ha⟩
  refine ⟨?_, ?_, ?_, himage⟩
  · intro k
    have h := s.property.1 k
    rw [← himage k] at h
    exact Finset.Nonempty.of_image h
  · intro k
    rw [← Finset.card_image_of_injective _ hl, himage k]
    exact s.property.2.1 k
  · intro k j hkj
    apply (Finset.disjoint_image hl).mp
    rw [himage k, himage j]
    exact s.property.2.2.1 k j hkj

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
