import HolomorphicAnosov.Topology.CairnsInitialFrontierGaps
import HolomorphicAnosov.Topology.CairnsAffineChordReversal

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsStar CairnsRefinement

/-- The literal initial map is affine on every actual frontier gap chord.
Choose a point of the parameter gap and a star arc containing it. The star's
local front gap is the same complementary component, so it has the same
unordered endpoints. The radial patch is affine there and agrees with the
initial map on its closed star. Reversal of endpoints replaces t by 1-t. -/
theorem cairns_initial_map_gap_affine
    {σ : Circle → ℂ} {a : Set ℂ} {p q : Circle}
    (hσ : Topology.IsEmbedding σ) (h : range σ ≃ₜ Circle) (d : InitialData σ a p q)
    (h₁ : StarGeometry d.firstStar h) (h₂ : StarGeometry d.secondStar h)
    (hcl : closure (d.stage h).region =
      closure d.firstStar.sourceStar ∪ closure d.secondStar.sourceStar)
    (hmap₁ : ∀ z ∈ range σ ∪ closure d.firstStar.sourceStar,
      (d.stage h).map z = d.firstStar.patchMap h z)
    (hmap₂ : ∀ z ∈ range σ ∪ closure d.secondStar.sourceStar,
      (d.stage h).map z = d.secondStar.patchMap h z)
    (g : CairnsCircleGap) (hg : g.IsGapOf ((d.stage h).contacts σ)) :
    ∀ t : I, (d.stage h).map ((1-(t : ℝ)) • σ g.first + (t : ℝ) • σ g.last) =
      (1-(t : ℝ)) • (h ⟨σ g.first,⟨g.first,rfl⟩⟩ : ℂ) +
        (t : ℝ) • (h ⟨σ g.last,⟨g.last,rfl⟩⟩ : ℂ) := by
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
  have htransfer {g' : CairnsCircleGap} (b : StarChoice σ a g')
      (hb : StarGeometry b h) (hv : CairnsCircleGap)
      (hvT : hv.IsGapOf ((d.stage h).contacts σ)) (hxv : x ∈ hv.openArc)
      (hch : openSegment ℝ (σ hv.first) (σ hv.last) ⊆ b.front ∩ a)
      (haff : ∀ t : I, b.patchMap h ((1-(t : ℝ)) • σ hv.first + (t : ℝ) • σ hv.last) =
        (1-(t : ℝ)) • (h ⟨σ hv.first,⟨hv.first,rfl⟩⟩ : ℂ) +
          (t : ℝ) • (h ⟨σ hv.last,⟨hv.last,rfl⟩⟩ : ℂ))
      (hmap : ∀ z ∈ range σ ∪ closure b.sourceStar, (d.stage h).map z = b.patchMap h z) :
      ∀ t : I, (d.stage h).map ((1-(t : ℝ)) • σ g.first + (t : ℝ) • σ g.last) =
        (1-(t : ℝ)) • (h ⟨σ g.first,⟨g.first,rfl⟩⟩ : ℂ) +
          (t : ℝ) • (h ⟨σ g.last,⟨g.last,rfl⟩⟩ : ℂ) := by
    have hchcl : segment ℝ (σ hv.first) (σ hv.last) ⊆ closure b.sourceStar := by
      intro z hz
      have hopencl : openSegment ℝ (σ hv.first) (σ hv.last) ⊆ closure b.sourceStar := by
        intro w hw
        exact frontier_subset_closure (show w ∈ frontier b.sourceStar from
          hb.2.2.2.1 ▸ Or.inr (hch hw).1)
      have hclosed := closure_mono hopencl (segment_subset_closure_openSegment hz)
      simpa only [closure_closure] using hclosed
    apply cairns_affine_chord_unordered_endpoints σ
      (fun t ↦ (h ⟨σ t,⟨t,rfl⟩⟩ : ℂ)) (d.stage h).map g.first g.last hv.first hv.last
      (cairns_gaps_equal_of_common_point _ g hv hg hvT x hxarc hxv).2
    intro t
    have hz : (1-(t : ℝ)) • σ hv.first + (t : ℝ) • σ hv.last ∈ closure b.sourceStar :=
      hchcl ⟨1-t,t,sub_nonneg.mpr t.property.2,t.property.1,sub_add_cancel _ _,rfl⟩
    rw [hmap _ (Or.inr hz)]
    exact haff t
  have hxcover : x ∈ d.firstGap.closedArc ∪ d.secondGap.closedArc := hcover.symm ▸ mem_univ x
  rcases hxcover with hx₁ | hx₂
  · obtain ⟨v,hv,hxv,hch,haff⟩ := cairns_star_missing_contact_global_gap hσ d.firstStar h h₁
      _ hlocal₁ x hx₁ hx
    exact htransfer d.firstStar h₁ v hv hxv hch haff hmap₁
  · obtain ⟨v,hv,hxv,hch,haff⟩ := cairns_star_missing_contact_global_gap hσ d.secondStar h h₂
      _ hlocal₂ x hx₂ hx
    exact htransfer d.secondStar h₂ v hv hxv hch haff hmap₂

end HolomorphicAnosov.Topology.Plane
