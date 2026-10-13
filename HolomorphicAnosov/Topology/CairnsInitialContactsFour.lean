import HolomorphicAnosov.Topology.CairnsResidualStageContacts

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- The initial literal datum retains the two chord endpoints and the two
interior first contacts on opposite parameter arcs. The endpoint contacts
are limits of the included open base and the other two are limits of the
included radial seams. Opposite arcs share only endpoints, giving four
distinct contacts before any successor has been chosen. This is the initial
case of Cairns §4(B,C), needed to construct the first successor. -/
theorem cairns_initial_contacts_four
    {σ : Circle → ℂ} {a : Set ℂ} {p q : Circle} {h : range σ ≃ₜ Circle}
    (hpq : p ≠ q) (d : InitialData σ a p q) :
    ∃ t₁ t₂ t₃ t₄ : Circle,
      t₁ ∈ (d.stage h).contacts σ ∧ t₂ ∈ (d.stage h).contacts σ ∧
      t₃ ∈ (d.stage h).contacts σ ∧ t₄ ∈ (d.stage h).contacts σ ∧
      t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₁ ≠ t₄ ∧ t₂ ≠ t₃ ∧ t₂ ≠ t₄ ∧ t₃ ≠ t₄ := by
  let i := d
  let r := i.firstGap.parameter i.firstStar.contactParameter
  let s := i.secondGap.parameter i.secondStar.contactParameter
  have hf₂ : i.secondGap.first = i.firstGap.last := by
    simp only [CairnsCircleGap.first, CairnsCircleGap.last, i.second_start]
  have hl₂ : i.secondGap.last = i.firstGap.first := by
    simp only [CairnsCircleGap.first, CairnsCircleGap.last, i.second_stop]
    exact Circle.periodic_exp _
  obtain ⟨hrp, hrq⟩ := cairns_star_contact_parameter_ne_endpoints i.firstStar
  obtain ⟨hsq, hsp⟩ := cairns_star_contact_parameter_ne_endpoints i.secondStar
  have hrp' : r ≠ p := by simpa only [r, i.first_eq] using hrp
  have hrq' : r ≠ q := by simpa only [r, i.last_eq] using hrq
  have hsp' : s ≠ p := by simpa only [s, hl₂, i.first_eq] using hsp
  have hsq' : s ≠ q := by simpa only [s, hf₂, i.last_eq] using hsq
  have hrs : r ≠ s := by
    intro hrs
    have hm : r ∈ range i.firstGap.parameter ∩ range i.secondGap.parameter :=
      ⟨⟨i.firstStar.contactParameter, rfl⟩, ⟨i.secondStar.contactParameter, hrs.symm⟩⟩
    rw [(CairnsCircleGap.opposite_parameter_cover_inter i.firstGap i.secondGap
      i.second_start i.second_stop hf₂ hl₂).2] at hm
    rcases hm with hr | hr
    · exact hrp hr
    · exact hrq hr
  have hchord : openSegment ℝ (σ p) (σ q) ⊆ (d.stage h).region := by
    exact subset_union_right
  have hp0 : p ∈ (d.stage h).contacts σ :=
    closure_mono hchord (segment_subset_closure_openSegment (left_mem_segment ℝ _ _))
  have hq0 : q ∈ (d.stage h).contacts σ :=
    closure_mono hchord (segment_subset_closure_openSegment (right_mem_segment ℝ _ _))
  have hr0 : r ∈ (d.stage h).contacts σ := by
    change σ r ∈ closure (d.stage h).region
    exact closure_mono (show i.firstStar.sourceStar ⊆ (i.stage h).region from
      fun z hz ↦ Or.inl (Or.inl hz)) (cairns_star_contact_mem_closure_sourceStar i.firstStar)
  have hs0 : s ∈ (d.stage h).contacts σ := by
    change σ s ∈ closure (d.stage h).region
    exact closure_mono (show i.secondStar.sourceStar ⊆ (i.stage h).region from
      fun z hz ↦ Or.inl (Or.inr hz)) (cairns_star_contact_mem_closure_sourceStar i.secondStar)
  exact ⟨p,q,r,s,hp0,hq0,hr0,hs0,hpq,hrp'.symm,hsp'.symm,hrq'.symm,hsq'.symm,hrs⟩

end HolomorphicAnosov.Topology.Plane

