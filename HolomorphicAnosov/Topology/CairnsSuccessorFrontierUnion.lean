import HolomorphicAnosov.Topology.CairnsGeometricStarChoice

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- After all old seams are inserted, the successor frontier is the old
curve contacts together with all new fronts. Closed-star overlap outside the
old carrier is impossible. A new front meets an old base only at original
curve endpoints, so no new front is swallowed by an old region, another star,
or an old seam. Source: Cairns §4(C), successive front replacement. -/
theorem cairns_successor_frontier_union
    {σ : Circle → ℂ} {a : Set ℂ} {s : Stage}
    (d : StepData σ a s) (h : range σ ≃ₜ Circle)
    (hgeo : ∀ i, StarGeometry (d.star i) h)
    (hsopen : IsOpen s.region) (hopen : IsOpen (d.next h).region)
    (hcurve : Disjoint (d.next h).region (range σ))
    (hcl : closure (d.next h).region = closure s.region ∪ ⋃ i, closure (d.star i).sourceStar)
    (holdfront : frontier s.region = σ '' s.contacts σ ∪
      ⋃ i, openSegment ℝ (σ (d.gap i).first) (σ (d.gap i).last))
    (hchord : ∀ i, openSegment ℝ (σ (d.gap i).first) (σ (d.gap i).last) ⊆ closure s.region)
    (hinter : ∀ i, closure s.region ∩ closure (d.star i).sourceStar =
      segment ℝ (σ (d.gap i).first) (σ (d.gap i).last))
    (hfrontbase : ∀ i, (d.star i).front ∩
      segment ℝ (σ (d.gap i).first) (σ (d.gap i).last) ⊆ range σ)
    (hoverlap : ∀ i j, i ≠ j → closure (d.star i).sourceStar ∩ closure (d.star j).sourceStar ⊆
      closure s.region ∪ range σ) :
    frontier (d.next h).region = σ '' s.contacts σ ∪ ⋃ i, (d.star i).front := by
  have hfrontcl : ∀ i, (d.star i).front ⊆ closure (d.star i).sourceStar := by
    intro i z hz
    exact frontier_subset_closure ((hgeo i).2.2.2.1 ▸ Or.inr hz)
  rw [hopen.frontier_eq,hcl]
  apply Subset.antisymm
  · rintro z ⟨hz,hnot⟩
    rcases hz with hz | hz
    · have hfr : z ∈ frontier s.region := by
        rw [hsopen.frontier_eq]
        exact ⟨hz,fun hh ↦ hnot (Or.inl hh)⟩
      rw [holdfront] at hfr
      rcases hfr with hc | hb
      · exact Or.inl hc
      · obtain ⟨i,hi⟩ := mem_iUnion.mp hb
        exact (hnot (Or.inr (mem_iUnion.mpr ⟨i,Or.inr hi⟩))).elim
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hz
      have hfr : z ∈ frontier (d.star i).sourceStar := by
        rw [(hgeo i).2.1.frontier_eq]
        exact ⟨hi,fun hh ↦ hnot (Or.inr (mem_iUnion.mpr ⟨i,Or.inl hh⟩))⟩
      rw [(hgeo i).2.2.2.1] at hfr
      rcases hfr with hb | hf
      · by_cases hc : z ∈ range σ
        · obtain ⟨t,rfl⟩ := hc
          exact Or.inl ⟨t,((hinter i).symm ▸ hb).1,rfl⟩
        · have hne₁ : σ (d.gap i).first ≠ z := fun he ↦ hc (he ▸ mem_range_self _)
          have hne₂ : σ (d.gap i).last ≠ z := fun he ↦ hc (he ▸ mem_range_self _)
          exact (hnot (Or.inr (mem_iUnion.mpr ⟨i,Or.inr
            (mem_openSegment_of_ne_left_right hne₁ hne₂ hb)⟩))).elim
      · exact Or.inr (mem_iUnion.mpr ⟨i,hf⟩)
  · rintro z (hz | hz)
    · obtain ⟨t,ht,rfl⟩ := hz
      exact ⟨Or.inl ht,fun hh ↦ disjoint_left.mp hcurve hh (mem_range_self _)⟩
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hz
      refine ⟨Or.inr (mem_iUnion.mpr ⟨i,hfrontcl i hi⟩),?_⟩
      intro hznext
      have hnc : z ∉ range σ := fun hc ↦ disjoint_left.mp hcurve hznext hc
      have hnotold : z ∉ closure s.region := by
        intro hzold
        exact hnc (hfrontbase i ⟨hi,hinter i ▸ ⟨hzold,hfrontcl i hi⟩⟩)
      rcases hznext with hzold | hznew
      · exact hnotold (subset_closure hzold)
      · obtain ⟨j,hj | hj⟩ := mem_iUnion.mp hznew
        · by_cases hij : i = j
          · subst j
            have hfr : z ∈ frontier (d.star i).sourceStar := (hgeo i).2.2.2.1 ▸ Or.inr hi
            rw [(hgeo i).2.1.frontier_eq] at hfr
            exact hfr.2 hj
          · exact (hoverlap i j hij ⟨hfrontcl i hi,subset_closure hj⟩).elim hnotold hnc
        · exact hnotold (hchord j hj)

end HolomorphicAnosov.Topology.Plane

