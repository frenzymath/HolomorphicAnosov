import HolomorphicAnosov.Topology.CairnsStarGlobalGaps
import HolomorphicAnosov.Topology.CairnsInitialContacts

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsStar CairnsRefinement

/-- All actual initial-stage complementary chords lie on the source frontier
and in the original region. Pick a missing parameter in the actual gap; one
of the two original arcs contains it. The corresponding star produces a local
front gap containing the same parameter. These are the same component, hence
have the same unordered endpoints and the same open chord. -/
theorem cairns_initial_gap_chord_frontier
    {σ : Circle → ℂ} {a : Set ℂ} {p q : Circle}
    (hσ : Topology.IsEmbedding σ) (h : range σ ≃ₜ Circle) (d : InitialData σ a p q)
    (h₁ : StarGeometry d.firstStar h) (h₂ : StarGeometry d.secondStar h)
    (hcl : closure (d.stage h).region =
      closure d.firstStar.sourceStar ∪ closure d.secondStar.sourceStar)
    (hfront : frontier (d.stage h).region = d.firstStar.front ∪ d.secondStar.front)
    (g : CairnsCircleGap) (hg : g.IsGapOf ((d.stage h).contacts σ)) :
    openSegment ℝ (σ g.first) (σ g.last) ⊆ frontier (d.stage h).region ∩ a := by
  obtain ⟨hT,hlocal₁,hlocal₂⟩ := cairns_initial_contacts_on_arcs hσ h d h₁ h₂ hcl
  obtain ⟨x,hx,hxg⟩ := hg.2.2
  have hxarc : x ∈ g.openArc := hxg ▸ mem_connectedComponentIn hx
  have hf₂ : d.secondGap.first = d.firstGap.last := by
    change Circle.exp d.secondGap.start = Circle.exp d.firstGap.stop
    rw [d.second_start]
  have hl₂ : d.secondGap.last = d.firstGap.first := by
    change Circle.exp d.secondGap.stop = Circle.exp d.firstGap.start
    rw [d.second_stop,Circle.periodic_exp]
  have hcover := (CairnsCircleGap.opposite_parameter_cover_inter d.firstGap d.secondGap
    d.second_start d.second_stop hf₂ hl₂).1
  rw [(CairnsCircleGap.parameter_embedding_range d.firstGap).2.1,
    (CairnsCircleGap.parameter_embedding_range d.secondGap).2.1] at hcover
  have hxcover : x ∈ d.firstGap.closedArc ∪ d.secondGap.closedArc := hcover.symm ▸ mem_univ x
  have htransfer (v : CairnsCircleGap) (hv : v.IsGapOf ((d.stage h).contacts σ))
      (hxv : x ∈ v.openArc) (hch : openSegment ℝ (σ v.first) (σ v.last) ⊆
        frontier (d.stage h).region ∩ a) :
      openSegment ℝ (σ g.first) (σ g.last) ⊆ frontier (d.stage h).region ∩ a := by
    have he := (cairns_gaps_equal_of_common_point _ g v hg hv x hxarc hxv).2
    rcases pair_eq_pair_iff.mp he with he | he
    · simpa only [he.1,he.2] using hch
    · simpa only [he.1,he.2,openSegment_symm] using hch
  rcases hxcover with hx₁ | hx₂
  · obtain ⟨v,hv,hxv,hch,haff⟩ := cairns_star_missing_contact_global_gap hσ d.firstStar h h₁
      _ hlocal₁ x hx₁ hx
    apply htransfer v hv hxv
    intro z hz
    exact ⟨hfront ▸ Or.inl (hch hz).1,(hch hz).2⟩
  · obtain ⟨v,hv,hxv,hch,haff⟩ := cairns_star_missing_contact_global_gap hσ d.secondStar h h₂
      _ hlocal₂ x hx₂ hx
    apply htransfer v hv hxv
    intro z hz
    exact ⟨hfront ▸ Or.inr (hch hz).1,(hch hz).2⟩

/-- With any complete labeling of actual complementary components, the initial
frontier is exactly its contacts plus the union of its labeled open chords.
The forward inclusion uses local star-front gap coverage; the reverse uses
the preceding actual-gap chord theorem and the fact that original-curve
contacts are outside the open region. -/
theorem cairns_initial_frontier_contact_chords
    {σ : Circle → ℂ} {a : Set ℂ} {p q : Circle}
    (hσ : Topology.IsEmbedding σ)
    (ha : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (h : range σ ≃ₜ Circle) (d : InitialData σ a p q)
    (h₁ : StarGeometry d.firstStar h) (h₂ : StarGeometry d.secondStar h)
    (hcl : closure (d.stage h).region =
      closure d.firstStar.sourceStar ∪ closure d.secondStar.sourceStar)
    (hfront : frontier (d.stage h).region = d.firstStar.front ∪ d.secondStar.front)
    (hopen : IsOpen (d.stage h).region) (hsub : (d.stage h).region ⊆ a)
    (gap : ResidualComponent ((d.stage h).contacts σ) → CairnsCircleGap)
    (hg : ∀ i, (gap i).IsGapOf ((d.stage h).contacts σ))
    (hgarc : ∀ i, (gap i).openArc = i.val) :
    frontier (d.stage h).region = σ '' (d.stage h).contacts σ ∪
      ⋃ i, openSegment ℝ (σ (gap i).first) (σ (gap i).last) := by
  obtain ⟨hT,hlocal₁,hlocal₂⟩ := cairns_initial_contacts_on_arcs hσ h d h₁ h₂ hcl
  have hcov (z : ℂ) (hz : z ∈ d.firstStar.front ∪ d.secondStar.front) (hzc : z ∉ range σ) :
      ∃ g : CairnsCircleGap, g.IsGapOf ((d.stage h).contacts σ) ∧
        z ∈ openSegment ℝ (σ g.first) (σ g.last) := by
    rcases hz with hz | hz
    · obtain ⟨g,hg,hzg,hch⟩ := cairns_star_front_global_gap_coverage hσ d.firstStar h h₁ _ hlocal₁ z hz hzc
      exact ⟨g,hg,hzg⟩
    · obtain ⟨g,hg,hzg,hch⟩ := cairns_star_front_global_gap_coverage hσ d.secondStar h h₂ _ hlocal₂ z hz hzc
      exact ⟨g,hg,hzg⟩
  apply Subset.antisymm
  · intro z hz
    by_cases hzc : z ∈ range σ
    · obtain ⟨t,rfl⟩ := hzc
      exact Or.inl ⟨t,frontier_subset_closure hz,rfl⟩
    · obtain ⟨g,hg',hzg⟩ := hcov z (hfront ▸ hz) hzc
      let i : ResidualComponent ((d.stage h).contacts σ) := ⟨g.openArc,hg'.2.2⟩
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
  · intro z hz
    rcases hz with hz | hz
    · obtain ⟨t,ht,rfl⟩ := hz
      rw [hopen.frontier_eq]
      refine ⟨ht,?_⟩
      intro hta
      obtain ⟨x,hx,he⟩ := ha
      have hmem : σ t ∈ connectedComponentIn (range σ)ᶜ x := he.symm ▸ hsub hta
      exact connectedComponentIn_subset _ _ hmem (mem_range_self t)
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hz
      exact (cairns_initial_gap_chord_frontier hσ h d h₁ h₂ hcl hfront (gap i) (hg i) hi).1

end HolomorphicAnosov.Topology.Plane
