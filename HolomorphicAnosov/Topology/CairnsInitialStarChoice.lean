import HolomorphicAnosov.Topology.CairnsResidualStarRefinement
import HolomorphicAnosov.Topology.Plane.CairnsChordSectorSeparation
import HolomorphicAnosov.Topology.CairnsInitialGapBookkeeping
import HolomorphicAnosov.Topology.CairnsGapParameter
import HolomorphicAnosov.Topology.PolygonEndpointIntersectionImage
import HolomorphicAnosov.Topology.Plane.CairnsInitialStarChoiceAssembly

namespace HolomorphicAnosov.Topology.Plane

open Set CairnsStar CairnsRefinement

/-! A generic compactness lemma for first contact along a path entering a closed set. -/
theorem cairns_first_contact_parameter
    {X : Type*} [TopologicalSpace X]
    (f : unitInterval → X) (hf : Continuous f) (K : Set X)
    (hK : IsClosed K) (h0 : f 0 ∉ K) (h1 : f 1 ∈ K) :
    ∃ t : unitInterval, 0 < (t : ℝ) ∧ f t ∈ K ∧
      ∀ s : unitInterval, s < t → f s ∉ K := by
  have hclosed : IsClosed (f ⁻¹' K) := hK.preimage hf
  obtain ⟨t, ht, hleast⟩ := hclosed.isCompact.exists_isLeast ⟨1, h1⟩
  have ht0 : t ≠ 0 := by
    intro he
    exact h0 (he ▸ ht)
  have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1
    (fun he ↦ ht0 (Subtype.ext he.symm))
  refine ⟨t, htpos, ht, ?_⟩
  intro s hst hsK
  exact (not_le_of_gt hst) (hleast hsK)

/-!
# Cairns first-contact source-star choices

Source: Cairns (1951), §3(D,E), printed pp.862–863.  For the two opposite
parameter gaps determined by the initial chord, the perpendicular ray in each
chord sector has a positive first contact with the corresponding curve arc.
The resulting sector, contact parameter, sign, radius, and first-contact
equation form the two `StarChoice` records used by `InitialData`.

DAG node: topo.cairns_initial_star_choice_g20.
-/
/-- Package the output of the convex-star provider when its angular path is the
gap parameter. This keeps the geometric first-contact existence in the provider
while exposing the exact `StarChoice` record needed by the recurrence. -/
theorem cairns_star_choice_of_convex_provider
    (σ : Circle → ℂ) (hσ : Topology.IsEmbedding σ)
    (g : CairnsCircleGap) (α α' : CairnsStar.I → Circle)
    (hpq : g.first ≠ g.last)
    (hα : Topology.IsEmbedding α) (hα' : Topology.IsEmbedding α')
    (hα0 : α ⟨0, by simp⟩ = g.first) (hα1 : α ⟨1, by simp⟩ = g.last)
    (hα'0 : α' ⟨0, by simp⟩ = g.first) (hα'1 : α' ⟨1, by simp⟩ = g.last)
    (hCover : Set.range α ∪ Set.range α' = Set.univ)
    (hMeet : Set.range α ∩ Set.range α' = {g.first, g.last})
    (a β : Set ℂ) (ha : a.Nonempty) (haBounded : Bornology.IsBounded a)
    (haComponent : ∃ x ∈ a, connectedComponentIn (Set.range σ)ᶜ x = a)
    (hChord : openSegment ℝ (σ g.first) (σ g.last) ⊆ a)
    (hβ : ∃ x ∈ a \ openSegment ℝ (σ g.first) (σ g.last),
      connectedComponentIn (a \ openSegment ℝ (σ g.first) (σ g.last)) x = β)
    (hFrontier : frontier β ⊆ segment ℝ (σ g.first) (σ g.last) ∪ σ '' g.closedArc)
    (hFrontierα : frontier β ⊆ segment ℝ (σ g.first) (σ g.last) ∪ σ '' Set.range α)
    (h : (Set.range σ) ≃ₜ Circle)
    (hparam : g.parameter = α) : ∃ s : StarChoice σ a g, s.sector = β := by
  obtain ⟨ε, τ, sP, hε, hτ, hs0, hs1, hP, hray, _⟩ :=
    cairns_convex_star_sector_extension σ hσ g.first g.last hpq
      α α' hα hα' hα0 hα1 hα'0 hα'1 hCover hMeet a β ha haBounded
      haComponent hChord hβ hFrontierα h
  obtain ⟨x, hx, hcomp⟩ := hβ
  let s : StarChoice σ a g :=
    { sector := β
      component := ⟨x, hx, hcomp⟩
      frontier_subset := hFrontier
      sign := ε
      sign_eq := hε
      radius := τ
      radius_pos := hτ
      contactParameter := sP
      contact_pos := hs0
      contact_lt_one := hs1
      first_contact := by simpa [hparam] using hP
      ray_inside := by intro t ht; exact hray t ht }
  exact ⟨s, rfl⟩

/-- Convert the sector frontier statement expressed through the chosen gap
parameter into the closed-arc form required by `StarChoice`. -/
theorem cairns_frontier_subset_gap_closedArc_of_parameter
    (σ : Circle → ℂ) (g : CairnsCircleGap) (α : CairnsStar.I → Circle)
    (β : Set ℂ)
    (hparam : g.parameter = α)
    (hFrontierα : frontier β ⊆
      segment ℝ (σ g.first) (σ g.last) ∪ σ '' Set.range α) :
    frontier β ⊆ segment ℝ (σ g.first) (σ g.last) ∪ σ '' g.closedArc := by
  have hrange : Set.range α = g.closedArc := by
    rw [← hparam]
    exact (CairnsCircleGap.parameter_embedding_range g).2.1
  simpa [hrange] using hFrontierα


end HolomorphicAnosov.Topology.Plane

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsStar CairnsRefinement

/-- Specialize chord-sector separation to consecutive opposite gap parameters,
rewriting its two frontier bounds in declared closed-arc form. -/
theorem cairns_opposite_gap_sector_frontier_data
    (σ : Circle → ℂ) (hσ : Topology.IsEmbedding σ)
    (a : Set ℂ) (ha : a.Nonempty) (haBounded : Bornology.IsBounded a)
    (haComponent : ∃ z ∈ a, connectedComponentIn (range σ)ᶜ z = a)
    (p q : Circle) (hpq : p ≠ q)
    (hChord : openSegment ℝ (σ p) (σ q) ⊆ a)
    (g₁ g₂ : CairnsCircleGap)
    (hg₁first : g₁.first = p) (hg₁last : g₁.last = q)
    (hg₂first : g₂.first = q) (hg₂last : g₂.last = p)
    (hstart : g₂.start = g₁.stop)
    (hstop : g₂.stop = g₁.start + 2 * Real.pi) :
    ∃ β₁ β₂ : Set ℂ,
      β₁.Nonempty ∧ β₂.Nonempty ∧ IsConnected β₁ ∧ IsConnected β₂ ∧
      IsOpen β₁ ∧ IsOpen β₂ ∧ Disjoint β₁ β₂ ∧
      a \ openSegment ℝ (σ p) (σ q) = β₁ ∪ β₂ ∧
      (∀ z ∈ a \ openSegment ℝ (σ p) (σ q),
        connectedComponentIn (a \ openSegment ℝ (σ p) (σ q)) z = β₁ ∨
          connectedComponentIn (a \ openSegment ℝ (σ p) (σ q)) z = β₂) ∧
      frontier β₁ ⊆ segment ℝ (σ p) (σ q) ∪ σ '' g₁.closedArc ∧
      frontier β₂ ⊆ segment ℝ (σ p) (σ q) ∪ σ '' g₂.closedArc := by
  obtain ⟨hα, hα', hα0, hα1, hα'0, hα'1, hCover, hMeet⟩ :=
    CairnsCircleGap.opposite_parameter_chord_arc_data g₁ g₂ hstart hstop
      (by simp [hg₂first, hg₁last]) (by simp [hg₂last, hg₁first])
  let rev₂ : unitInterval → Circle := fun t => g₂.parameter (unitInterval.symm t)
  obtain ⟨β₁, β₂, hβ₁n, hβ₂n, hβ₁c, hβ₂c, hβ₁o, hβ₂o, hdisj,
      hUnion, hComp, hFront₁, hFront₂, _⟩ :=
    cairns_chord_sector_separation σ hσ p q hpq g₁.parameter rev₂
      hα hα' (by simpa [hg₁first] using hα0) (by simpa [hg₁last] using hα1)
      (by simpa [rev₂, hg₂last, hg₁first] using hα'0)
      (by simpa [rev₂, hg₂first, hg₁last] using hα'1)
      (by simpa [hg₁first, hg₁last] using hCover)
      (by simpa [hg₁first, hg₁last] using hMeet) a ha haBounded haComponent hChord
  have hr₁ : range g₁.parameter = g₁.closedArc :=
    (CairnsCircleGap.parameter_embedding_range g₁).2.1
  have hrevRange : range rev₂ = range g₂.parameter := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨unitInterval.symm t, by simp [rev₂]⟩
    · rintro ⟨t, rfl⟩
      exact ⟨unitInterval.symm t, by simp [rev₂]⟩
  have hr₂ : range rev₂ = g₂.closedArc := by
    rw [hrevRange]
    exact (CairnsCircleGap.parameter_embedding_range g₂).2.1
  rw [hr₁] at hFront₁
  rw [hr₂] at hFront₂
  exact ⟨β₁, β₂, hβ₁n, hβ₂n, hβ₁c, hβ₂c, hβ₁o, hβ₂o, hdisj,
    hUnion, hComp, hFront₁, hFront₂⟩

end HolomorphicAnosov.Topology.Plane

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsStar CairnsRefinement

/-- Under the two opposite-sector hypotheses, apply the convex-star provider in
both orientations and package its first-contact outputs as the two StarChoices. -/
theorem cairns_opposite_gap_star_choices_of_convex_provider
    (σ : Circle → ℂ) (hσ : Topology.IsEmbedding σ)
    (a : Set ℂ) (ha : a.Nonempty) (haBounded : Bornology.IsBounded a)
    (haComponent : ∃ z ∈ a, connectedComponentIn (range σ)ᶜ z = a)
    (p q : Circle) (hpq : p ≠ q)
    (hChord : openSegment ℝ (σ p) (σ q) ⊆ a)
    (g₁ g₂ : CairnsCircleGap)
    (hg₁first : g₁.first = p) (hg₁last : g₁.last = q)
    (hg₂first : g₂.first = q) (hg₂last : g₂.last = p)
    (hstart : g₂.start = g₁.stop)
    (hstop : g₂.stop = g₁.start + 2 * Real.pi)
    (h : (range σ) ≃ₜ Circle) :
    Nonempty (StarChoice σ a g₁ × StarChoice σ a g₂) := by
  obtain ⟨β₁, β₂, hβ₁n, hβ₂n, hβ₁c, hβ₂c, hβ₁o, hβ₂o, hdisj,
      hUnion, hComp, hFront₁, hFront₂⟩ :=
    cairns_opposite_gap_sector_frontier_data σ hσ a ha haBounded haComponent
      p q hpq hChord g₁ g₂ hg₁first hg₁last hg₂first hg₂last hstart hstop
  have hβ₁ : ∃ x ∈ a \ openSegment ℝ (σ p) (σ q),
      connectedComponentIn (a \ openSegment ℝ (σ p) (σ q)) x = β₁ := by
    obtain ⟨x, hx⟩ := hβ₁n
    have hxU : x ∈ a \ openSegment ℝ (σ p) (σ q) := by
      rw [hUnion]
      exact Or.inl hx
    rcases hComp x hxU with hc | hc
    · exact ⟨x, hxU, hc⟩
    · have hx₂ : x ∈ β₂ := by rw [← hc]; exact mem_connectedComponentIn hxU
      exact (hdisj.le_bot ⟨hx, hx₂⟩).elim
  have hβ₂ : ∃ x ∈ a \ openSegment ℝ (σ p) (σ q),
      connectedComponentIn (a \ openSegment ℝ (σ p) (σ q)) x = β₂ := by
    obtain ⟨x, hx⟩ := hβ₂n
    have hxU : x ∈ a \ openSegment ℝ (σ p) (σ q) := by
      rw [hUnion]
      exact Or.inr hx
    rcases hComp x hxU with hc | hc
    · have hx₁ : x ∈ β₁ := by rw [← hc]; exact mem_connectedComponentIn hxU
      exact (hdisj.le_bot ⟨hx₁, hx⟩).elim
    · exact ⟨x, hxU, hc⟩
  have hparam₁ : g₁.parameter = g₁.parameter := rfl
  have hparam₂ : g₂.parameter = g₂.parameter := rfl
  have hfront₁α : frontier β₁ ⊆ segment ℝ (σ p) (σ q) ∪ σ '' range g₁.parameter := by
    simpa only [(CairnsCircleGap.parameter_embedding_range g₁).2.1] using hFront₁
  have hfront₂α : frontier β₂ ⊆ segment ℝ (σ p) (σ q) ∪ σ '' range g₂.parameter := by
    simpa only [(CairnsCircleGap.parameter_embedding_range g₂).2.1] using hFront₂
  have hFront₁' : frontier β₁ ⊆ segment ℝ (σ g₁.first) (σ g₁.last) ∪ σ '' g₁.closedArc := by
    simpa [hg₁first, hg₁last] using hFront₁
  have hFront₂' : frontier β₂ ⊆ segment ℝ (σ g₂.first) (σ g₂.last) ∪ σ '' g₂.closedArc := by
    simpa [hg₂first, hg₂last, segment_symm] using hFront₂
  have hfront₁α' : frontier β₁ ⊆ segment ℝ (σ g₁.first) (σ g₁.last) ∪ σ '' range g₁.parameter := by
    simpa [hg₁first, hg₁last] using hfront₁α
  have hfront₂α' : frontier β₂ ⊆ segment ℝ (σ g₂.first) (σ g₂.last) ∪ σ '' range g₂.parameter := by
    simpa [hg₂first, hg₂last, segment_symm] using hfront₂α
  have hChord₁ : openSegment ℝ (σ g₁.first) (σ g₁.last) ⊆ a := by
    simpa [hg₁first, hg₁last] using hChord
  have hChord₂ : openSegment ℝ (σ g₂.first) (σ g₂.last) ⊆ a := by
    simpa [hg₂first, hg₂last, openSegment_symm] using hChord
  have hpq₁ : g₁.first ≠ g₁.last := by
    intro he
    apply hpq
    exact hg₁first.symm.trans (he.trans hg₁last)
  have hpq₂ : g₂.first ≠ g₂.last := by
    intro he
    apply hpq
    exact (hg₂first.symm.trans (he.trans hg₂last)).symm
  have hβ₁' : ∃ x ∈ a \ openSegment ℝ (σ g₁.first) (σ g₁.last),
      connectedComponentIn (a \ openSegment ℝ (σ g₁.first) (σ g₁.last)) x = β₁ := by
    simpa [hg₁first, hg₁last] using hβ₁
  have hβ₂' : ∃ x ∈ a \ openSegment ℝ (σ g₂.first) (σ g₂.last),
      connectedComponentIn (a \ openSegment ℝ (σ g₂.first) (σ g₂.last)) x = β₂ := by
    simpa [hg₂first, hg₂last, openSegment_symm] using hβ₂
  obtain ⟨ha₁, ha₂, ha₁0, ha₁1, ha₂0, ha₂1, hCover₁, hMeet₁⟩ :=
    CairnsCircleGap.opposite_parameter_chord_arc_data g₁ g₂ hstart hstop
      (by simp [hg₂first, hg₁last]) (by simp [hg₂last, hg₁first])
  obtain ⟨s₁, hs₁⟩ := cairns_star_choice_of_convex_provider σ hσ g₁
      g₁.parameter (fun t : CairnsStar.I => g₂.parameter (unitInterval.symm t))
      hpq₁
      ha₁ ha₂ ha₁0 ha₁1 ha₂0 ha₂1 hCover₁ hMeet₁ a β₁ ha haBounded haComponent
      hChord₁ hβ₁' hFront₁' hfront₁α' h hparam₁
  obtain ⟨hb₁, hb₂, hb₁0, hb₁1, hb₂0, hb₂1, hCover₂, hMeet₂⟩ :=
    CairnsCircleGap.opposite_parameter_chord_arc_data_reverse g₁ g₂ hstart hstop
      (by simp [hg₂first, hg₁last]) (by simp [hg₂last, hg₁first])
  obtain ⟨s₂, hs₂⟩ := cairns_star_choice_of_convex_provider σ hσ g₂
      g₂.parameter (fun t : CairnsStar.I => g₁.parameter (unitInterval.symm t))
      hpq₂
      hb₁ hb₂ hb₁0 hb₁1 hb₂0 hb₂1 hCover₂ hMeet₂ a β₂ ha haBounded haComponent
      hChord₂ hβ₂' hFront₂' hfront₂α' h hparam₂
  exact ⟨(s₁, s₂)⟩

theorem cairns_initial_star_choice_source_obligation
    (σ : Circle → ℂ) (hσ : Topology.IsEmbedding σ)
    (a : Set ℂ) (ha : a.Nonempty) (haBounded : Bornology.IsBounded a)
    (haComponent : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (p q : Circle) (hpq : p ≠ q)
    (hChord : openSegment ℝ (σ p) (σ q) ⊆ a)
    (_hStar : True) :
    ∃ d : InitialData σ a p q,
      d.firstGap.first = p ∧ d.firstGap.last = q := by
  obtain ⟨g₁, g₂, hp₁, hq₁, hp₂, hq₂, hstart, hstop⟩ :=
    cairns_initial_gap_bookkeeping_source_obligation p q hpq
  obtain ⟨⟨s₁, s₂⟩⟩ := cairns_opposite_gap_star_choices_of_convex_provider
      σ hσ a ha haBounded haComponent p q hpq hChord g₁ g₂ hp₁ hq₁ hp₂ hq₂
      hstart hstop hσ.toHomeomorph.symm
  exact cairns_initial_star_choice_assembly g₁ g₂ hp₁ hq₁ hp₂ hq₂ hstart hstop s₁ s₂


end HolomorphicAnosov.Topology.Plane
