import HolomorphicAnosov.Topology.CairnsOutsideSectorSelection

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- Three retained contacts make every gap chord a proper part of the stage
frontier. A retained contact outside the gap's closed arc differs from both
endpoints; if it were on the chord, it would be on its open segment inside the
original component, contradicting its membership in the original curve.
Source: Cairns §4(C), proper seam arcs. -/
theorem cairns_gap_proper_frontier_chord
    {σ : Circle → ℂ} {a : Set ℂ} {s : Stage}
    (hσ : Topology.IsEmbedding σ)
    (ha : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (hthree : ∃ p q r : Circle, p ∈ s.contacts σ ∧ q ∈ s.contacts σ ∧ r ∈ s.contacts σ ∧
      p ≠ q ∧ p ≠ r ∧ q ≠ r)
    (hsopen : IsOpen s.region) (hsa : s.region ⊆ a)
    (g : CairnsCircleGap) (hg : g.IsGapOf (s.contacts σ))
    (hchord : openSegment ℝ (σ g.first) (σ g.last) ⊆ a) :
    segment ℝ (σ g.first) (σ g.last) ≠ frontier s.region := by
  obtain ⟨t,ht,htout⟩ := cairns_gap_exists_contact_outside g (s.contacts σ) hg hthree
  obtain ⟨x,hx,hcomp⟩ := ha
  have hac : a ⊆ (range σ)ᶜ := hcomp ▸ connectedComponentIn_subset (range σ)ᶜ x
  have htfront : σ t ∈ frontier s.region := by
    rw [hsopen.frontier_eq]
    exact ⟨ht,fun hh ↦ hac (hsa hh) (mem_range_self t)⟩
  intro he
  have htseg : σ t ∈ segment ℝ (σ g.first) (σ g.last) := he.symm ▸ htfront
  have hfirst : σ g.first ≠ σ t := by
    intro hh
    apply htout
    rw [← hσ.injective hh]
    exact ⟨g.start,⟨le_rfl,g.start_lt_stop.le⟩,rfl⟩
  have hlast : σ g.last ≠ σ t := by
    intro hh
    apply htout
    rw [← hσ.injective hh]
    exact ⟨g.stop,⟨g.start_lt_stop.le,le_rfl⟩,rfl⟩
  exact hac (hchord (mem_openSegment_of_ne_left_right hfirst hlast htseg)) (mem_range_self t)

end HolomorphicAnosov.Topology.Plane

