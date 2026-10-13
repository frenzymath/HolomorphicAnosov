import HolomorphicAnosov.Topology.CairnsPatchGluing

namespace HolomorphicAnosov
open Set

/-- Glue a continuous map on a compact base and an arbitrary compact family
of patches. Each piece maps bijectively to its target. Target patches overlap
only in the old target base, and each patch/base intersection maps onto the
corresponding target intersection. Thus a cross-patch collision lifts to the
old base, where injectivity identifies its preimages. Compactness upgrades the
resulting continuous bijection to a homeomorphism. Source: Cairns §4(C). -/
theorem compact_base_patches_homeomorph
    {E F ι : Type*} [TopologicalSpace E] [TopologicalSpace F] [T2Space F]
    (B : Set E) (C : Set F) (K : ι → Set E) (L : ι → Set F) (f : E → F)
    (hcompact : IsCompact (B ∪ ⋃ i, K i))
    (hcont : ContinuousOn f (B ∪ ⋃ i, K i))
    (hbase : BijOn f B C) (hpatch : ∀ i, BijOn f (K i) (L i))
    (hinter : ∀ i, f '' (B ∩ K i) = C ∩ L i)
    (hoverlap : ∀ i j, i ≠ j → L i ∩ L j ⊆ C) :
    ∃ H : ↥(B ∪ ⋃ i, K i) ≃ₜ ↥(C ∪ ⋃ i, L i), ∀ x, (H x : F) = f x := by
  classical
  let : CompactSpace ↥(B ∪ ⋃ i, K i) := isCompact_iff_compactSpace.mp hcompact
  have hreflect : ∀ i x, x ∈ K i → f x ∈ C → x ∈ B := by
    intro i x hx hfx
    have hh : f x ∈ f '' (B ∩ K i) := (hinter i).symm ▸ ⟨hfx,(hpatch i).mapsTo hx⟩
    obtain ⟨y,hy,he⟩ := hh
    have hxy := (hpatch i).injOn hx hy.2 he.symm
    exact hxy.symm ▸ hy.1
  have hmaps : MapsTo f (B ∪ ⋃ i, K i) (C ∪ ⋃ i, L i) := by
    rintro x (hx | hx)
    · exact Or.inl (hbase.mapsTo hx)
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact Or.inr (mem_iUnion.mpr ⟨i,(hpatch i).mapsTo hi⟩)
  have hinj : InjOn f (B ∪ ⋃ i, K i) := by
    intro x hx y hy he
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hbase.injOn hx hy he
    · obtain ⟨j,hj⟩ := mem_iUnion.mp hy
      exact hbase.injOn hx (hreflect j y hj (he ▸ hbase.mapsTo hx)) he
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact hbase.injOn (hreflect i x hi (he.symm ▸ hbase.mapsTo hy)) hy he
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      obtain ⟨j,hj⟩ := mem_iUnion.mp hy
      by_cases hij : i = j
      · subst j
        exact (hpatch i).injOn hi hj he
      · have hfx : f x ∈ C := hoverlap i j hij
          ⟨(hpatch i).mapsTo hi,he.symm ▸ (hpatch j).mapsTo hj⟩
        exact hbase.injOn (hreflect i x hi hfx) (hreflect j y hj (he ▸ hfx)) he
  have hsurj : SurjOn f (B ∪ ⋃ i, K i) (C ∪ ⋃ i, L i) := by
    rintro y (hy | hy)
    · obtain ⟨x,hx,he⟩ := hbase.surjOn hy
      exact ⟨x,Or.inl hx,he⟩
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hy
      obtain ⟨x,hx,he⟩ := (hpatch i).surjOn hi
      exact ⟨x,Or.inr (mem_iUnion.mpr ⟨i,hx⟩),he⟩
  let F' : ↥(B ∪ ⋃ i, K i) → ↥(C ∪ ⋃ i, L i) := fun x ↦ ⟨f x,hmaps x.property⟩
  have hbij : Function.Bijective F' := by
    constructor
    · intro x y he
      exact Subtype.ext (hinj x.property y.property (congrArg Subtype.val he))
    · intro y
      obtain ⟨x,hx,he⟩ := hsurj y.property
      exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  have hc : Continuous F' :=
    (continuousOn_iff_continuous_domRestrict.mp hcont).subtype_mk _
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F' hbij) hc,fun x ↦ rfl⟩

end HolomorphicAnosov

