import HolomorphicAnosov.Topology.CairnsGeometricStarChoice
import HolomorphicAnosov.Topology.CairnsResidualInitialData

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsStar CairnsRefinement

/-- Choose the initial datum with geometric disk stars in the two disjoint
opposite sectors. The existing initial choice supplies the lifted angular
endpoints. Chord separation labels the two actual sectors; applying the full
single-star provider separately to those sectors retains all geometry needed
for the initial-cell gluing, rather than discarding it from the witnesses. -/
theorem cairns_geometric_initial_choice
    (σ : Circle → ℂ) (hσ : Topology.IsEmbedding σ)
    (a : Set ℂ) (ha : a.Nonempty) (habounded : Bornology.IsBounded a)
    (hacomp : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (h : range σ ≃ₜ Circle) (p q : Circle) (hpq : p ≠ q)
    (hchord : openSegment ℝ (σ p) (σ q) ⊆ a) :
    ∃ d : InitialData σ a p q,
      StarGeometry d.firstStar h ∧ StarGeometry d.secondStar h ∧
      IsOpen d.firstStar.sector ∧ IsOpen d.secondStar.sector ∧
      Disjoint d.firstStar.sector d.secondStar.sector := by
  obtain ⟨d,hdp,hdq⟩ := cairns_residual_initial_data_source_obligation
    σ hσ a ha habounded hacomp h p q hpq hchord trivial
  have hg2first : d.secondGap.first = q := by
    change Circle.exp d.secondGap.start = q
    rw [d.second_start]
    exact d.last_eq
  have hg2last : d.secondGap.last = p := by
    change Circle.exp d.secondGap.stop = p
    rw [d.second_stop,Circle.periodic_exp]
    exact d.first_eq
  obtain ⟨β₁,β₂,hβ₁ne,hβ₂ne,hβ₁conn,hβ₂conn,hβ₁open,hβ₂open,hdisj,
    hunion,hcomponents,hfront₁,hfront₂⟩ := cairns_opposite_gap_sector_frontier_data
      σ hσ a ha habounded hacomp p q hpq hchord d.firstGap d.secondGap
      d.first_eq d.last_eq hg2first hg2last d.second_start d.second_stop
  have hcomp₁ : ∃ x ∈ a \ openSegment ℝ (σ p) (σ q),
      connectedComponentIn (a \ openSegment ℝ (σ p) (σ q)) x = β₁ := by
    obtain ⟨x,hx⟩ := hβ₁ne
    have hxcut : x ∈ a \ openSegment ℝ (σ p) (σ q) := hunion ▸ Or.inl hx
    refine ⟨x,hxcut,?_⟩
    rcases hcomponents x hxcut with hh | hh
    · exact hh
    · have hxm : x ∈ β₂ := hh ▸ mem_connectedComponentIn hxcut
      exact (Set.disjoint_left.mp hdisj hx hxm).elim
  have hcomp₂ : ∃ x ∈ a \ openSegment ℝ (σ p) (σ q),
      connectedComponentIn (a \ openSegment ℝ (σ p) (σ q)) x = β₂ := by
    obtain ⟨x,hx⟩ := hβ₂ne
    have hxcut : x ∈ a \ openSegment ℝ (σ p) (σ q) := hunion ▸ Or.inr hx
    refine ⟨x,hxcut,?_⟩
    rcases hcomponents x hxcut with hh | hh
    · have hxm : x ∈ β₁ := hh ▸ mem_connectedComponentIn hxcut
      exact (Set.disjoint_left.mp hdisj hxm hx).elim
    · exact hh
  obtain ⟨b₁,hb₁sector,hb₁⟩ := cairns_geometric_star_choice σ hσ a ha habounded hacomp
    d.firstGap (by simpa only [d.first_eq,d.last_eq] using hchord) β₁
    (by simpa only [d.first_eq,d.last_eq] using hcomp₁)
    (by simpa only [d.first_eq,d.last_eq] using hfront₁) h
  obtain ⟨b₂,hb₂sector,hb₂⟩ := cairns_geometric_star_choice σ hσ a ha habounded hacomp
    d.secondGap (by simpa only [hg2first,hg2last,openSegment_symm] using hchord) β₂
    (by simpa only [hg2first,hg2last,openSegment_symm] using hcomp₂)
    (by simpa only [hg2first,hg2last,segment_symm] using hfront₂) h
  refine ⟨{d with firstStar := b₁,secondStar := b₂},hb₁,hb₂,?_,?_,?_⟩
  · simpa only [hb₁sector] using hβ₁open
  · simpa only [hb₂sector] using hβ₂open
  · simpa only [hb₁sector,hb₂sector] using hdisj

end HolomorphicAnosov.Topology.Plane
