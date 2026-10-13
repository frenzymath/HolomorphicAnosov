import HolomorphicAnosov.Topology.SegmentProperAmbientCircleArc

open Set
namespace HolomorphicAnosov

/-- A straight segment contained in a simple interval arc is exactly the subarc
between its endpoint parameters. Source: Cairns (1951), §3(D), p.863, with the
interval monotonicity argument made explicit. Parametrize the straight segment
injectively and compose with the inverse arc parametrization. This is a continuous
injection of the interval into itself, hence monotone or antitone. The intermediate
value theorem identifies its range with the unordered closed interval between
its endpoints. Applying the original arc gives the claimed identity. -/
theorem arc_contained_segment_g2 (L : Set ℂ) (α : unitInterval ≃ₜ L)
    (u v : unitInterval)
    (hseg : segment ℝ (α u).1 (α v).1 ⊆ L) :
    (fun t ↦ (α t).1) '' uIcc u v = segment ℝ (α u).1 (α v).1 := by
  by_cases huv : u=v
  · subst v
    simp
  have hUV : (α u).1 ≠ (α v).1 := fun he ↦ huv (α.injective (Subtype.ext he))
  obtain ⟨f,hf,hfr,hf0,hf1⟩ := segment_embedded_arc (α u).1 (α v).1 hUV
  let F : unitInterval → L := fun t ↦ ⟨f t,hseg (hfr ▸ mem_range_self t)⟩
  let g : unitInterval → unitInterval := α.symm ∘ F
  have hF : Continuous F := hf.continuous.subtype_mk _
  have hg : Continuous g := α.symm.continuous.comp hF
  have hgi : Function.Injective g := by
    intro x y h
    exact hf.injective (congrArg Subtype.val (α.symm.injective h))
  have hg0 : g 0=u := by
    apply α.injective
    change α (α.symm (F 0))=α u
    rw [α.apply_symm_apply]
    exact Subtype.ext hf0
  have hg1 : g 1=v := by
    apply α.injective
    change α (α.symm (F 1))=α v
    rw [α.apply_symm_apply]
    exact Subtype.ext hf1
  have hinterval : uIcc (0:unitInterval) 1=univ := by
    ext t
    simp only [uIcc_of_le (show (0:unitInterval) ≤ 1 from zero_le_one),mem_Icc,mem_univ,iff_true]
    exact ⟨bot_le,le_top⟩
  have hrange : range g=uIcc u v := by
    rcases hg.strictMono_of_inj hgi with hm | ha
    · have he := hg.continuousOn.image_uIcc_of_monotoneOn (a:=0) (b:=1)
        (hm.monotone.monotoneOn _)
      simpa only [hinterval,image_univ,hg0,hg1] using he
    · have he := hg.continuousOn.image_uIcc_of_antitoneOn (a:=0) (b:=1)
        (ha.antitone.antitoneOn _)
      simpa only [hinterval,image_univ,hg0,hg1] using he
  rw [← hrange,← range_comp]
  have hfun : (fun t ↦ (α (g t)).1)=f := by
    funext t
    exact congrArg Subtype.val (α.apply_symm_apply (F t))
  exact congrArg range hfun |>.trans hfr

lemma arc_contained_openSegment_g2 (L : Set ℂ) (α : unitInterval ≃ₜ L)
    (u v : unitInterval) (huv : u < v)
    (hseg : segment ℝ (α u).1 (α v).1 ⊆ L) :
    (fun t ↦ (α t).1) '' Ioo u v = openSegment ℝ (α u).1 (α v).1 := by
  have hclosed := arc_contained_segment_g2 L α u v hseg
  rw [uIcc_of_le huv.le] at hclosed
  have hinj : Function.Injective (fun t ↦ (α t).1) := Subtype.val_injective.comp α.injective
  apply Subset.antisymm
  · rintro z ⟨t,ht,rfl⟩
    exact mem_openSegment_of_ne_left_right (hinj.ne ht.1.ne) (hinj.ne ht.2.ne')
      (hclosed ▸ mem_image_of_mem _ ⟨ht.1.le,ht.2.le⟩)
  · intro z hz
    obtain ⟨t,ht,he⟩ := (hclosed.symm ▸ openSegment_subset_segment ℝ _ _ hz :
      z ∈ (fun t ↦ (α t).1) '' Icc u v)
    refine ⟨t,⟨lt_of_le_of_ne ht.1 ?_,lt_of_le_of_ne ht.2 ?_⟩,he⟩
    · intro hut
      subst t
      have heq : (α u).1=(α v).1 := left_mem_openSegment_iff.mp (he.symm ▸ hz)
      exact huv.ne (hinj heq)
    · intro htv
      subst t
      have heq : (α u).1=(α v).1 := right_mem_openSegment_iff.mp (he.symm ▸ hz)
      exact huv.ne (hinj heq)

end HolomorphicAnosov
