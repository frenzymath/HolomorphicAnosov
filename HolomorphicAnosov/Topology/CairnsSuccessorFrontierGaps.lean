import HolomorphicAnosov.Topology.CairnsSuccessorGapAffine

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- The successor outer-front union is exactly retained curve contacts plus
the chords of its actual complementary gaps. Local star-front coverage gives
the forward inclusion, and the successor-gap refinement theorem gives the
reverse inclusion. Component labels differ at most by endpoint orientation.
Source: Cairns §4(C), frontier invariant. -/
theorem cairns_successor_frontier_contact_chords
    {σ : Circle → ℂ} {a : Set ℂ} {s : Stage}
    (hσ : Topology.IsEmbedding σ) (d : StepData σ a s) (h : range σ ≃ₜ Circle)
    (hgeo : ∀ i, StarGeometry (d.star i) h)
    (hT : (d.next h).contacts σ = s.contacts σ ∪
      ⋃ i, σ ⁻¹' ((d.star i).front ∩ range σ))
    (hpatch : ∀ i z, z ∈ closure (d.star i).sourceStar →
      (d.next h).map z = (d.star i).patchMap h z)
    (hfront : frontier (d.next h).region = σ '' s.contacts σ ∪ ⋃ i, (d.star i).front)
    (hopen : IsOpen (d.next h).region)
    (hcurve : Disjoint (d.next h).region (range σ))
    (gap : ResidualComponent ((d.next h).contacts σ) → CairnsCircleGap)
    (hg : ∀ i, (gap i).IsGapOf ((d.next h).contacts σ))
    (hgarc : ∀ i, (gap i).openArc = i.val) :
    frontier (d.next h).region = σ '' (d.next h).contacts σ ∪
      ⋃ i, openSegment ℝ (σ (gap i).first) (σ (gap i).last) := by
  apply Subset.antisymm
  · intro z hz
    by_cases hzc : z ∈ range σ
    · obtain ⟨t,rfl⟩ := hzc
      exact Or.inl ⟨t,frontier_subset_closure hz,rfl⟩
    · have hf := hfront ▸ hz
      rcases hf with hc | hf
      · exact (hzc (image_subset_range _ _ hc)).elim
      · obtain ⟨j,hj⟩ := mem_iUnion.mp hf
        obtain ⟨g,hg',hzg,hch⟩ := cairns_star_front_global_gap_coverage hσ (d.star j) h (hgeo j)
          _ (cairns_successor_contacts_on_gap hσ d h hgeo hT j) z hj hzc
        let i : ResidualComponent ((d.next h).contacts σ) := ⟨g.openArc,hg'.2.2⟩
        have heq : (gap i).openArc = g.openArc := hgarc i
        obtain ⟨x,hx,hxe⟩ := hg'.2.2
        have hxg : x ∈ g.openArc := hxe ▸ mem_connectedComponentIn hx
        have hep := (cairns_gaps_equal_of_common_point _ (gap i) g (hg i) hg' x
          (heq.symm ▸ hxg) hxg).2
        right
        apply mem_iUnion.mpr
        refine ⟨i,?_⟩
        rcases pair_eq_pair_iff.mp hep with he | he
        · simpa only [he.1,he.2] using hzg
        · simpa only [he.1,he.2,openSegment_symm] using hzg
  · rintro z (hz | hz)
    · obtain ⟨t,ht,rfl⟩ := hz
      rw [hopen.frontier_eq]
      exact ⟨ht,fun hh ↦ disjoint_left.mp hcurve hh (mem_range_self _)⟩
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hz
      obtain ⟨⟨j,hj⟩,haff⟩ := cairns_successor_gap_front_affine hσ d h hgeo hT hpatch (gap i) (hg i)
      rw [hfront]
      exact Or.inr (mem_iUnion.mpr ⟨j,(hj hi).1⟩)

end HolomorphicAnosov.Topology.Plane

