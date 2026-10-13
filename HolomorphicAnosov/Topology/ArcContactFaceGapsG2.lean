import HolomorphicAnosov.Topology.ArcContainedSegmentG2

open Set
namespace HolomorphicAnosov

/-- A contact-free parameter interval of an arc covered by straight contact faces
is exactly the corresponding straight open segment. Source: Cairns (1951), §3(D),
p.863; agent-written interval-barrier expansion. Choose one interior parameter
and a contact face containing its image. The inverse arc parameters of the face
endpoints bracket that parameter. As contacts cannot lie in the given interval,
those two endpoint parameters bracket the entire interval. The given interval's
endpoint images therefore belong to the face; their segment is contained in that
face and hence in the arc. The contained-segment subarc theorem identifies its
open segment with the desired open parameter interval. -/
theorem arc_contact_face_gap_g2 (L C : Set ℂ) (α : unitInterval ≃ₜ L)
    (hfaces : ∀ q ∈ L \ C, ∃ U V : ℂ, U ∈ L ∩ C ∧ V ∈ L ∩ C ∧
      q ∈ openSegment ℝ U V ∧ segment ℝ U V ⊆ L)
    (l r : unitInterval) (hlr : l<r)
    (hgap : ∀ t ∈ Ioo l r, (α t).1 ∉ C) :
    (fun t ↦ (α t).1) '' Ioo l r = openSegment ℝ (α l).1 (α r).1 := by
  obtain ⟨t,hlt,htr⟩ := exists_between hlr
  obtain ⟨U,V,hU,hV,htUV,hUV⟩ := hfaces (α t).1 ⟨(α t).2,hgap t ⟨hlt,htr⟩⟩
  let u := α.symm ⟨U,hU.1⟩
  let v := α.symm ⟨V,hV.1⟩
  have hu : (α u).1=U := congrArg Subtype.val (α.apply_symm_apply _)
  have hv : (α v).1=V := congrArg Subtype.val (α.apply_symm_apply _)
  have hseg : segment ℝ (α u).1 (α v).1 ⊆ L := by simpa only [hu,hv] using hUV
  have hclosed := arc_contained_segment_g2 L α u v hseg
  have hinj : Function.Injective (fun t ↦ (α t).1) := Subtype.val_injective.comp α.injective
  have htin : t ∈ uIcc u v := by
    have htimage : (α t).1 ∈ (fun s ↦ (α s).1) '' uIcc u v :=
      hclosed.symm ▸ (by simpa only [hu,hv] using openSegment_subset_segment ℝ U V htUV)
    exact hinj.mem_set_image.mp htimage
  have houtu : u ∉ Ioo l r := fun hi ↦ hgap u hi (hu.symm ▸ hU.2)
  have houtv : v ∉ Ioo l r := fun hi ↦ hgap v hi (hv.symm ▸ hV.2)
  have hbracket : Icc l r ⊆ uIcc u v := by
    rcases le_total u v with huv | hvu
    · rw [uIcc_of_le huv] at htin ⊢
      have hul : u ≤ l := by
        by_contra hn
        exact houtu ⟨lt_of_not_ge hn,lt_of_le_of_lt htin.1 htr⟩
      have hrv : r ≤ v := by
        by_contra hn
        exact houtv ⟨lt_of_lt_of_le hlt htin.2,lt_of_not_ge hn⟩
      exact fun z hz ↦ ⟨hul.trans hz.1,hz.2.trans hrv⟩
    · rw [uIcc_of_ge hvu] at htin ⊢
      have hvl : v ≤ l := by
        by_contra hn
        exact houtv ⟨lt_of_not_ge hn,lt_of_le_of_lt htin.1 htr⟩
      have hru : r ≤ u := by
        by_contra hn
        exact houtu ⟨lt_of_lt_of_le hlt htin.2,lt_of_not_ge hn⟩
      exact fun z hz ↦ ⟨hvl.trans hz.1,hz.2.trans hru⟩
  have hlface : (α l).1 ∈ segment ℝ (α u).1 (α v).1 :=
    hclosed ▸ mem_image_of_mem _ (hbracket ⟨le_rfl,hlr.le⟩)
  have hrface : (α r).1 ∈ segment ℝ (α u).1 (α v).1 :=
    hclosed ▸ mem_image_of_mem _ (hbracket ⟨hlr.le,le_rfl⟩)
  exact arc_contained_openSegment_g2 L α l r hlr
    (((convex_segment (α u).1 (α v).1).segment_subset hlface hrface).trans hseg)

end HolomorphicAnosov
