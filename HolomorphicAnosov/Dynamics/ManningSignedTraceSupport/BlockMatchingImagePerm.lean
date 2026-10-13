import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.BlockMatching

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open scoped Classical
noncomputable section

/-- An invariant finite block and an alphabet permutation induce a matching
between its images under two injective coordinate maps whenever each element
has a legal edge to the permuted element. Restrict the permutation to the block
and identify the block with each coordinate image. This handles both ordinary
successor edges and the return edge in Manning (1971), pp.218–219. -/
theorem blockMatching_image_perm {A : Type*} [DecidableEq A] {N : ℕ}
    (T : Matrix (Fin N) (Fin N) ℤ) (l r : A → Fin N)
    (hl : Function.Injective l) (hr : Function.Injective r)
    (g : A ≃ A) (s : Finset A) (hs : s.image g = s)
    (hedge : ∀ a ∈ s, T (l a) (r (g a)) = 1) :
    BlockMatching T (s.image l) (s.image r) := by
  classical
  let L : ↥s → ↥(s.image l) := fun a ↦ ⟨l a.val, Finset.mem_image_of_mem _ a.property⟩
  let R : ↥s → ↥(s.image r) := fun a ↦ ⟨r (g a.val), by
    apply Finset.mem_image_of_mem
    simpa only [hs] using Finset.mem_image_of_mem g a.property⟩
  have hL : Function.Bijective L := by
    constructor
    · intro a b h
      exact Subtype.ext (hl (congrArg Subtype.val h))
    · intro i
      obtain ⟨a, ha, hai⟩ := Finset.mem_image.mp i.property
      exact ⟨⟨a, ha⟩, Subtype.ext hai⟩
  have hR : Function.Bijective R := by
    constructor
    · intro a b h
      exact Subtype.ext (g.injective (hr (congrArg Subtype.val h)))
    · intro i
      obtain ⟨a, ha, hai⟩ := Finset.mem_image.mp i.property
      have hga : g.symm a ∈ s := by
        rw [← hs] at ha
        obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp ha
        simpa only [← hba, g.symm_apply_apply] using hb
      refine ⟨⟨g.symm a, hga⟩, Subtype.ext ?_⟩
      change r (g (g.symm a)) = i.val
      simpa only [g.apply_symm_apply] using hai
  let eL := Equiv.ofBijective L hL
  let eR := Equiv.ofBijective R hR
  refine ⟨eL.symm.trans eR, ?_⟩
  intro i
  have hi : l (eL.symm i).val = i.val := congrArg Subtype.val (eL.apply_symm_apply i)
  change T i.val (r (g (eL.symm i).val)) = 1
  rw [← hi]
  exact hedge _ (eL.symm i).property

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
