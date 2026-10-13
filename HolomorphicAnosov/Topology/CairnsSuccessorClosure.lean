import HolomorphicAnosov.Topology.CairnsResidualStarRefinement

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- The closed successor is the old closure together with the new closed
stars, provided that union is closed. Nullness of the star family supplies
closedness in the recurrence. Every added seam already lies in the old
closure; the reverse inclusion follows because each open star is added.
Source: Cairns §4(C), equation (4.3) and its accumulation argument. -/
theorem cairns_successor_region_closure
    {σ : Circle → ℂ} {a : Set ℂ} {h : range σ ≃ₜ Circle}
    {s : Stage} (d : StepData σ a s)
    (hclosed : IsClosed (closure s.region ∪ ⋃ i, closure (d.star i).sourceStar))
    (hseam : ∀ i, openSegment ℝ (σ (d.gap i).first) (σ (d.gap i).last) ⊆
      closure s.region) :
    closure (d.next h).region = closure s.region ∪ ⋃ i, closure (d.star i).sourceStar := by
  apply Subset.antisymm
  · apply closure_minimal _ hclosed
    rintro z (hz | hz)
    · exact Or.inl (subset_closure hz)
    · obtain ⟨i,hi | hi⟩ := mem_iUnion.mp hz
      · exact Or.inr (mem_iUnion.mpr ⟨i,subset_closure hi⟩)
      · exact Or.inl (hseam i hi)
  · apply union_subset
    · exact closure_mono subset_union_left
    · apply iUnion_subset
      intro i
      apply closure_mono
      intro z hz
      exact Or.inr (mem_iUnion.mpr ⟨i,Or.inl hz⟩)

/-- Once the closed successor is identified, its original-curve contacts are
precisely the old contacts and the contacts on new fronts. This uses inverse
images of the union and the single-star contact identity; it introduces no
new contact through accumulation. Source: Cairns §4(C), retained set S_j. -/
theorem cairns_successor_contacts
    {σ : Circle → ℂ} {a : Set ℂ} {h : range σ ≃ₜ Circle}
    {s : Stage} (d : StepData σ a s)
    (hclosure : closure (d.next h).region =
      closure s.region ∪ ⋃ i, closure (d.star i).sourceStar)
    (hcontacts : ∀ i, range σ ∩ closure (d.star i).sourceStar =
      (d.star i).front ∩ range σ) :
    (d.next h).contacts σ = s.contacts σ ∪
      ⋃ i, σ ⁻¹' ((d.star i).front ∩ range σ) := by
  ext t
  change σ t ∈ closure (d.next h).region ↔ _
  rw [hclosure]
  constructor
  · rintro (ht | ht)
    · exact Or.inl ht
    · obtain ⟨i,hi⟩ := mem_iUnion.mp ht
      exact Or.inr (mem_iUnion.mpr ⟨i,hcontacts i ▸ ⟨mem_range_self t,hi⟩⟩)
  · rintro (ht | ht)
    · exact Or.inl ht
    · obtain ⟨i,hi⟩ := mem_iUnion.mp ht
      have hh : σ t ∈ range σ ∩ closure (d.star i).sourceStar :=
        (hcontacts i).symm ▸ hi
      exact Or.inr (mem_iUnion.mpr ⟨i,hh.2⟩)

end HolomorphicAnosov.Topology.Plane

