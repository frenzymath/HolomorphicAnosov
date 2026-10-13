import HolomorphicAnosov.Topology.CairnsCompactBasePatchGluing
import HolomorphicAnosov.Topology.CairnsGeometricStarChoice

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsStar CairnsRefinement

/-- Simultaneous pasting gives the literal successor carrier homeomorphism.
The curve is included in every patch. Each patch meets the old carrier in
the curve and its base chord, whose images are prescribed identically. The
target separation hypotheses prevent collisions between different patches.
Source: Cairns §4(C), extension of the prescribed homeomorphism. -/
theorem cairns_successor_carrier_homeomorph
    {σ : Circle → ℂ} {a : Set ℂ} {s : Stage}
    (d : StepData σ a s) (h : range σ ≃ₜ Circle)
    (hgeo : ∀ i, StarGeometry (d.star i) h)
    (H₀ : ↥(closure s.region ∪ range σ) ≃ₜ
      ↥(closure s.target ∪ range (fun z : Circle ↦ (z : ℂ))))
    (hH₀ : ∀ x, (H₀ x : ℂ) = s.map x)
    (hcurve : ∀ (z : ℂ) (hz : z ∈ range σ), s.map z = (h ⟨z,hz⟩ : ℂ))
    (hpatch : ∀ i z, z ∈ closure (d.star i).sourceStar →
      (d.next h).map z = (d.star i).patchMap h z)
    (hcompact : IsCompact ((closure s.region ∪ range σ) ∪ ⋃ i, closure (d.star i).sourceStar))
    (hcont : ContinuousOn (d.next h).map
      ((closure s.region ∪ range σ) ∪ ⋃ i, closure (d.star i).sourceStar))
    (hsource : ∀ i, closure s.region ∩ closure (d.star i).sourceStar =
      segment ℝ (σ (d.gap i).first) (σ (d.gap i).last))
    (htarget : ∀ i, closure ((d.star i).targetStar h) ∩ closure s.target =
      segment ℝ (h ⟨σ (d.gap i).first,⟨(d.gap i).first,rfl⟩⟩ : ℂ)
        (h ⟨σ (d.gap i).last,⟨(d.gap i).last,rfl⟩⟩ : ℂ))
    (hoverlap : ∀ i j, i ≠ j → closure ((d.star i).targetStar h) ∩
      closure ((d.star j).targetStar h) ⊆ closure s.target) :
    ∃ H : ↥((closure s.region ∪ range σ) ∪ ⋃ i, closure (d.star i).sourceStar) ≃ₜ
      ↥((closure s.target ∪ range (fun z : Circle ↦ (z : ℂ))) ∪
        ⋃ i, closure ((d.star i).targetStar h)),
      ∀ x, (H x : ℂ) = (d.next h).map x := by
  classical
  let c := range σ
  let k := range (fun z : Circle ↦ (z : ℂ))
  let B := closure s.region ∪ c
  let C := closure s.target ∪ k
  let K := fun i ↦ c ∪ closure (d.star i).sourceStar
  let L := fun i ↦ k ∪ closure ((d.star i).targetStar h)
  let f := (d.next h).map
  have hold : ∀ z ∈ B, f z = s.map z := by
    intro z hz
    change (if z ∈ closure s.region ∪ range σ then s.map z else _) = _
    exact ite_eq_left hz
  have hfc : ∀ (z : ℂ) (hz : z ∈ c), f z = (h ⟨z,hz⟩ : ℂ) := by
    intro z hz
    exact (hold z (Or.inr hz)).trans (hcurve z hz)
  have heq : ∀ i z, z ∈ K i → f z = (d.star i).patchMap h z := by
    intro i z hz
    rcases hz with hz | hz
    · rw [hfc z hz]
      change z ∈ range σ at hz
      simp only [StarChoice.patchMap,dite_eq_left hz]
    · exact hpatch i z hz
  have hbij (U V : Set ℂ) (H : U ≃ₜ V) (he : ∀ x, (H x : ℂ) = f x) : BijOn f U V := by
    refine ⟨?_,?_,?_⟩
    · intro x hx
      rw [← he ⟨x,hx⟩]
      exact (H ⟨x,hx⟩).property
    · intro x hx y hy hxy
      apply congrArg Subtype.val (H.injective (show H ⟨x,hx⟩ = H ⟨y,hy⟩ from ?_))
      apply Subtype.ext
      simpa only [he] using hxy
    · intro y hy
      obtain ⟨x,hx⟩ := H.surjective ⟨y,hy⟩
      exact ⟨x,x.property,(he x).symm.trans (congrArg Subtype.val hx)⟩
  have hBbij : BijOn f B C := hbij B C H₀ (fun x ↦ (hH₀ x).trans (hold x x.property).symm)
  have hKbij : ∀ i, BijOn f (K i) (L i) := by
    intro i
    obtain ⟨H,hH,hrest⟩ := cairns_geometric_star_literal_extension (d.star i) h (hgeo i)
    exact hbij _ _ H (fun x ↦ (hH x).trans (heq i x x.property).symm)
  have hBK : ∀ i, B ∩ K i = c ∪ segment ℝ (σ (d.gap i).first) (σ (d.gap i).last) := by
    intro i
    have hh : B ∩ K i = c ∪ (closure s.region ∩ closure (d.star i).sourceStar) := by
      ext z; simp only [B,K,mem_union,mem_inter_iff]; tauto
    rw [hh,hsource]
  have hCL : ∀ i, C ∩ L i = k ∪
      segment ℝ (h ⟨σ (d.gap i).first,⟨(d.gap i).first,rfl⟩⟩ : ℂ)
        (h ⟨σ (d.gap i).last,⟨(d.gap i).last,rfl⟩⟩ : ℂ) := by
    intro i
    have hh : C ∩ L i = k ∪ (closure ((d.star i).targetStar h) ∩ closure s.target) := by
      ext z; simp only [C,L,mem_union,mem_inter_iff]; tauto
    rw [hh,htarget]
  have hinter : ∀ i, f '' (B ∩ K i) = C ∩ L i := by
    intro i
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact ⟨hBbij.mapsTo hx.1,(hKbij i).mapsTo hx.2⟩
    · rw [hCL]
      rintro y (hy | hy)
      · obtain ⟨yc,rfl⟩ := hy
        let x : range σ := h.symm yc
        refine ⟨x,?_,?_⟩
        · rw [hBK]
          exact Or.inl x.property
        · exact (hfc x x.property).trans (congrArg Subtype.val (h.apply_symm_apply yc))
      · rw [segment_eq_image] at hy
        obtain ⟨t,ht,rfl⟩ := hy
        let x : ℂ := (1-t) • σ (d.gap i).first + t • σ (d.gap i).last
        have hx : x ∈ B ∩ K i := by
          rw [hBK]
          exact Or.inr ⟨1-t,t,sub_nonneg.mpr ht.2,ht.1,sub_add_cancel _ _,rfl⟩
        refine ⟨x,hx,?_⟩
        rw [heq i x hx.2]
        obtain ⟨H,hH,hint,hbase,hrest⟩ := cairns_geometric_star_literal_extension (d.star i) h (hgeo i)
        exact hbase ⟨t,ht⟩
  have hinterpatch : ∀ i j, i ≠ j → L i ∩ L j ⊆ C := by
    intro i j hij z hz
    rcases hz.1 with hz₁ | hz₁
    · exact Or.inr hz₁
    · rcases hz.2 with hz₂ | hz₂
      · exact Or.inr hz₂
      · exact Or.inl (hoverlap i j hij ⟨hz₁,hz₂⟩)
  have hdom : B ∪ ⋃ i, K i = (closure s.region ∪ range σ) ∪ ⋃ i, closure (d.star i).sourceStar := by
    ext z
    simp only [B,K,c,mem_union,mem_iUnion]
    constructor
    · rintro (hz | ⟨i,hzi | hzi⟩)
      · exact Or.inl hz
      · exact Or.inl (Or.inr hzi)
      · exact Or.inr ⟨i,hzi⟩
    · rintro (hz | ⟨i,hi⟩)
      · exact Or.inl hz
      · exact Or.inr ⟨i,Or.inr hi⟩
  have hcod : C ∪ ⋃ i, L i = (closure s.target ∪ k) ∪ ⋃ i, closure ((d.star i).targetStar h) := by
    ext z
    simp only [C,L,mem_union,mem_iUnion]
    constructor
    · rintro (hz | ⟨i,hzi | hzi⟩)
      · exact Or.inl hz
      · exact Or.inl (Or.inr hzi)
      · exact Or.inr ⟨i,hzi⟩
    · rintro (hz | ⟨i,hi⟩)
      · exact Or.inl hz
      · exact Or.inr ⟨i,Or.inr hi⟩
  obtain ⟨H,hH⟩ := compact_base_patches_homeomorph B C K L f
    (hdom.symm ▸ hcompact) (hdom.symm ▸ hcont) hBbij hKbij hinter hinterpatch
  refine ⟨((Homeomorph.setCongr hdom).symm.trans H).trans (Homeomorph.setCongr hcod),?_⟩
  intro x
  exact hH ⟨x,hdom.symm ▸ x.property⟩

end HolomorphicAnosov.Topology.Plane

