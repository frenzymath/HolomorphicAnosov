import HolomorphicAnosov.Topology.CairnsNullPatchPasting

namespace HolomorphicAnosov
open Set

/-- Continuous compatible maps with compatible inverses glue to a
homeomorphism of a compact union. This is the set-theoretic pasting step in
Cairns §4(B,C): agreement is checked through one total map, and injectivity
across different pieces is checked by the overlap condition. -/
theorem compact_union_homeomorph_of_patch_maps
    {E F ι : Type*} [TopologicalSpace E] [TopologicalSpace F] [T2Space F]
    (K : ι → Set E) (L : ι → Set F) (f : E → F)
    (hcompact : IsCompact (⋃ i, K i)) (hcont : ContinuousOn f (⋃ i, K i))
    (hpatch : ∀ i, Set.BijOn f (K i) (L i))
    (hoverlap : ∀ i j x, x ∈ K i → f x ∈ L j → x ∈ K j) :
    ∃ H : ↥(⋃ i, K i) ≃ₜ ↥(⋃ i, L i), ∀ x, (H x : F) = f x := by
  classical
  let : CompactSpace (⋃ i, K i) := isCompact_iff_compactSpace.mp hcompact
  let F' : ↥(⋃ i, K i) → ↥(⋃ i, L i) := fun x ↦ ⟨f x,by
    obtain ⟨i,hi⟩ := mem_iUnion.mp x.property
    exact mem_iUnion.mpr ⟨i,(hpatch i).mapsTo hi⟩⟩
  have hinj : Function.Injective F' := by
    intro x y hxy
    obtain ⟨i,hi⟩ := mem_iUnion.mp x.property
    obtain ⟨j,hj⟩ := mem_iUnion.mp y.property
    have he : f x = f y := congrArg Subtype.val hxy
    have hxj : x.val ∈ K j := hoverlap i j x hi (he ▸ (hpatch j).mapsTo hj)
    exact Subtype.ext ((hpatch j).injOn hxj hj he)
  have hsurj : Function.Surjective F' := by
    intro y
    obtain ⟨i,hi⟩ := mem_iUnion.mp y.property
    obtain ⟨x,hx,hxy⟩ := (hpatch i).surjOn hi
    exact ⟨⟨x,mem_iUnion.mpr ⟨i,hx⟩⟩,Subtype.ext hxy⟩
  have hc : Continuous F' :=
    (continuousOn_iff_continuous_domRestrict.mp hcont).subtype_mk _
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F' ⟨hinj,hsurj⟩) hc,
    fun x ↦ rfl⟩

/-- Two compact patch maps glue if each is a homeomorphism onto its patch and
their common domain maps onto the common target. The latter condition prevents
collisions between different patches: lift a common image into the overlap,
then use injectivity within either patch. -/
theorem compact_two_patch_homeomorph
    {E F : Type*} [TopologicalSpace E] [T2Space E]
    [TopologicalSpace F] [T2Space F]
    (A₁ A₂ : Set E) (B₁ B₂ : Set F) (f : E → F)
    (hc₁ : IsCompact A₁) (hc₂ : IsCompact A₂)
    (hf₁ : ContinuousOn f A₁) (hf₂ : ContinuousOn f A₂)
    (hb₁ : BijOn f A₁ B₁) (hb₂ : BijOn f A₂ B₂)
    (hinter : f '' (A₁ ∩ A₂) = B₁ ∩ B₂) :
    ∃ H : ↥(A₁ ∪ A₂) ≃ₜ ↥(B₁ ∪ B₂), ∀ x, (H x : F) = f x := by
  classical
  let : CompactSpace ↥(A₁ ∪ A₂) := isCompact_iff_compactSpace.mp (hc₁.union hc₂)
  have hmaps : MapsTo f (A₁ ∪ A₂) (B₁ ∪ B₂) := by
    intro x hx
    exact hx.elim (fun hx ↦ Or.inl (hb₁.mapsTo hx)) (fun hx ↦ Or.inr (hb₂.mapsTo hx))
  have hcross {x y : E} (hx : x ∈ A₁) (hy : y ∈ A₂) (he : f x = f y) : x = y := by
    have him : f x ∈ f '' (A₁ ∩ A₂) := by
      rw [hinter]
      exact ⟨hb₁.mapsTo hx,he.symm ▸ hb₂.mapsTo hy⟩
    obtain ⟨z,hz,hze⟩ := him
    exact (hb₁.injOn hx hz.1 hze.symm).trans (hb₂.injOn hz.2 hy (hze.trans he))
  have hinj : InjOn f (A₁ ∪ A₂) := by
    intro x hx y hy he
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hb₁.injOn hx hy he
    · exact hcross hx hy he
    · exact (hcross hy hx he.symm).symm
    · exact hb₂.injOn hx hy he
  have hsurj : SurjOn f (A₁ ∪ A₂) (B₁ ∪ B₂) := by
    intro y hy
    rcases hy with hy | hy
    · obtain ⟨x,hx,he⟩ := hb₁.surjOn hy
      exact ⟨x,Or.inl hx,he⟩
    · obtain ⟨x,hx,he⟩ := hb₂.surjOn hy
      exact ⟨x,Or.inr hx,he⟩
  let F' : ↥(A₁ ∪ A₂) → ↥(B₁ ∪ B₂) := fun x ↦ ⟨f x,hmaps x.property⟩
  have hFbij : Function.Bijective F' := by
    constructor
    · intro x y he
      exact Subtype.ext (hinj x.property y.property (congrArg Subtype.val he))
    · intro y
      obtain ⟨x,hx,he⟩ := hsurj y.property
      exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  have hcont : Continuous F' :=
    (continuousOn_iff_continuous_domRestrict.mp
      (hf₁.union_of_isClosed hf₂ hc₁.isClosed hc₂.isClosed)).subtype_mk _
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F' hFbij) hcont,fun x ↦ rfl⟩

end HolomorphicAnosov
