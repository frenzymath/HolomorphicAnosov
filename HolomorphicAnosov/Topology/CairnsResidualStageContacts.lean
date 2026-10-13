import HolomorphicAnosov.Topology.CairnsResidualStarRecurrenceProperties
import HolomorphicAnosov.Topology.CairnsGapParameter

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- A first-contact parameter is different from both endpoints of its proper
angular gap. This follows from injectivity of the gap parametrization and the
strictly interior first-contact parameter in Cairns §3(D). -/
theorem cairns_star_contact_parameter_ne_endpoints
    {σ : Circle → ℂ} {a : Set ℂ} {g : CairnsCircleGap}
    (b : StarChoice σ a g) :
    g.parameter b.contactParameter ≠ g.first ∧
      g.parameter b.contactParameter ≠ g.last := by
  obtain ⟨he, _, h0, h1⟩ := CairnsCircleGap.parameter_embedding_range g
  constructor
  · intro h
    have ht := he.injective (h.trans h0.symm)
    have hv := congrArg (fun t : unitInterval ↦ (t : ℝ)) ht
    exact (ne_of_gt b.contact_pos) hv
  · intro h
    have ht := he.injective (h.trans h1.symm)
    have hv := congrArg (fun t : unitInterval ↦ (t : ℝ)) ht
    exact (ne_of_lt b.contact_lt_one) hv

/-- The retained contact is a closure point of the literal source star because
the latter contains the open segment from its center to this contact.
Source: Cairns §3(D), the seam included in the two-half star. -/
theorem cairns_star_contact_mem_closure_sourceStar
    {σ : Circle → ℂ} {a : Set ℂ} {g : CairnsCircleGap}
    (b : StarChoice σ a g) : b.contact ∈ closure b.sourceStar := by
  exact closure_mono (show openSegment ℝ b.center b.contact ⊆ b.sourceStar from
    subset_union_right) (segment_subset_closure_openSegment (right_mem_segment ℝ _ _))

/-- Every actual Cairns stage has a closed contact set with at least four
points: the original chord endpoints and the interior first contacts on its
two opposite arcs. Source: Cairns §4(B,C), pp.864–865. The chord endpoints are
limits of the initial open chord. Each first contact is a limit of its included
radial seam. The opposite proper arcs meet only at the chord endpoints, so the
four parameters are distinct. Monotonicity propagates them to every later
stage. Closedness follows by taking the inverse image of the closed region
under the continuous boundary embedding. This does not use an arbitrary-stage
sector invariant or any unproved geometric property of a star. -/
theorem cairns_residual_stage_contacts_four
    {σ : Circle → ℂ} {a : Set ℂ} {p q : Circle} {h : (range σ) ≃ₜ Circle}
    (hσ : Topology.IsEmbedding σ) (hpq : p ≠ q) (d : Data σ a p q h)
    (j : ℕ) :
    IsClosed ((d.stages j).contacts σ) ∧
      ∃ t₁ t₂ t₃ t₄ : Circle,
        t₁ ∈ (d.stages j).contacts σ ∧ t₂ ∈ (d.stages j).contacts σ ∧
        t₃ ∈ (d.stages j).contacts σ ∧ t₄ ∈ (d.stages j).contacts σ ∧
        t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₁ ≠ t₄ ∧ t₂ ≠ t₃ ∧ t₂ ≠ t₄ ∧ t₃ ≠ t₄ := by
  let i := d.initial
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
  have hchord : openSegment ℝ (σ p) (σ q) ⊆ (d.stages 0).region := by
    rw [d.start_eq]
    exact subset_union_right
  have hp0 : p ∈ (d.stages 0).contacts σ :=
    closure_mono hchord (segment_subset_closure_openSegment (left_mem_segment ℝ _ _))
  have hq0 : q ∈ (d.stages 0).contacts σ :=
    closure_mono hchord (segment_subset_closure_openSegment (right_mem_segment ℝ _ _))
  have hr0 : r ∈ (d.stages 0).contacts σ := by
    change σ r ∈ closure (d.stages 0).region
    rw [d.start_eq]
    exact closure_mono (show i.firstStar.sourceStar ⊆ (i.stage h).region from
      fun z hz ↦ Or.inl (Or.inl hz)) (cairns_star_contact_mem_closure_sourceStar i.firstStar)
  have hs0 : s ∈ (d.stages 0).contacts σ := by
    change σ s ∈ closure (d.stages 0).region
    rw [d.start_eq]
    exact closure_mono (show i.secondStar.sourceStar ⊆ (i.stage h).region from
      fun z hz ↦ Or.inl (Or.inr hz)) (cairns_star_contact_mem_closure_sourceStar i.secondStar)
  have hmono := (cairns_residual_star_recurrence_properties d).2.2.1 (Nat.zero_le j)
  exact ⟨isClosed_closure.preimage hσ.continuous,
    p, q, r, s, hmono hp0, hmono hq0, hmono hr0, hmono hs0,
    hpq, hrp'.symm, hsp'.symm, hrq'.symm, hsq'.symm, hrs⟩

end HolomorphicAnosov.Topology.Plane
