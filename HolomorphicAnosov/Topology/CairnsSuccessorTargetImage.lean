import HolomorphicAnosov.Topology.CairnsStarPatchHomeomorph

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsStar CairnsRefinement

/-- An endpoint-affine map carries the entire open source chord onto its
open target chord, including the degenerate endpoint case. Both chords are
the images of the same open unit interval. -/
theorem affine_chord_image_openSegment (f : ℂ → ℂ) (p q u v : ℂ)
    (haff : ∀ t : I, f ((1-(t : ℝ)) • p + (t : ℝ) • q) =
      (1-(t : ℝ)) • u + (t : ℝ) • v) :
    f '' openSegment ℝ p q = openSegment ℝ u v := by
  rw [openSegment_eq_image,openSegment_eq_image,image_image]
  apply image_congr
  intro t ht
  exact haff ⟨t,⟨ht.1.le,ht.2.le⟩⟩

/-- The literal successor has exactly the target union in equation (4.4).
Its old values are unchanged, each new open star maps onto its target star,
and each old open base chord maps affinely onto the corresponding target
chord. Images commute with the possibly empty, infinite union of patches.
Source: Cairns §4(C), equations (4.3)–(4.4). -/
theorem cairns_successor_target_image
    {σ : Circle → ℂ} {a : Set ℂ} {s : Stage}
    (d : StepData σ a s) (h : range σ ≃ₜ Circle)
    (hgeo : ∀ i, StarGeometry (d.star i) h)
    (hpatch : ∀ i z, z ∈ closure (d.star i).sourceStar →
      (d.next h).map z = (d.star i).patchMap h z)
    (hchord : ∀ i, openSegment ℝ (σ (d.gap i).first) (σ (d.gap i).last) ⊆ closure s.region)
    (haff : ∀ i (t : I),
      s.map ((1-(t : ℝ)) • σ (d.gap i).first + (t : ℝ) • σ (d.gap i).last) =
        (1-(t : ℝ)) • (h ⟨σ (d.gap i).first,⟨(d.gap i).first,rfl⟩⟩ : ℂ) +
          (t : ℝ) • (h ⟨σ (d.gap i).last,⟨(d.gap i).last,rfl⟩⟩ : ℂ)) :
    (d.next h).target = s.target ∪ ⋃ i,
      ((d.star i).targetStar h ∪
        openSegment ℝ (h ⟨σ (d.gap i).first,⟨(d.gap i).first,rfl⟩⟩ : ℂ)
          (h ⟨σ (d.gap i).last,⟨(d.gap i).last,rfl⟩⟩ : ℂ)) := by
  classical
  have hold : ∀ z ∈ closure s.region, (d.next h).map z = s.map z := by
    intro z hz
    change (if z ∈ closure s.region ∪ range σ then s.map z else _) = _
    exact ite_eq_left (Or.inl hz)
  change (d.next h).map '' (s.region ∪ ⋃ i,
    ((d.star i).sourceStar ∪ openSegment ℝ (σ (d.gap i).first) (σ (d.gap i).last))) = _
  rw [image_union,image_iUnion]
  congr 1
  · apply image_congr
    intro z hz
    exact hold z (subset_closure hz)
  · apply iUnion_congr
    intro i
    rw [image_union]
    congr 1
    · calc
        (d.next h).map '' (d.star i).sourceStar =
            (d.star i).patchMap h '' (d.star i).sourceStar :=
          image_congr (fun z hz ↦ hpatch i z (subset_closure hz))
        _ = _ := (cairns_star_patch_bijOn (d.star i) h (hgeo i)).2.2
    · calc
        (d.next h).map '' openSegment ℝ (σ (d.gap i).first) (σ (d.gap i).last) =
            s.map '' openSegment ℝ (σ (d.gap i).first) (σ (d.gap i).last) :=
          image_congr (fun z hz ↦ hold z (hchord i hz))
        _ = _ := affine_chord_image_openSegment _ _ _ _ _ (haff i)

end HolomorphicAnosov.Topology.Plane

