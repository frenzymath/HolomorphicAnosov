import HolomorphicAnosov.Topology.CairnsSuccessorLocalContacts
import HolomorphicAnosov.Topology.CairnsStarGlobalGaps
import HolomorphicAnosov.Topology.CairnsAffineChordReversal

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsStar CairnsRefinement

/-- Every successor gap refines an old gap and its chord belongs to that
old gap's new front. A missing successor contact is a missing old contact;
its old residual component chooses the star. Local contact agreement identifies
the star's front-gap component with the global successor gap. -/
theorem cairns_successor_gap_front_affine
    {σ : Circle → ℂ} {a : Set ℂ} {s : Stage}
    (hσ : Topology.IsEmbedding σ) (d : StepData σ a s) (h : range σ ≃ₜ Circle)
    (hgeo : ∀ i, StarGeometry (d.star i) h)
    (hT : (d.next h).contacts σ = s.contacts σ ∪
      ⋃ i, σ ⁻¹' ((d.star i).front ∩ range σ))
    (hpatch : ∀ i z, z ∈ closure (d.star i).sourceStar →
      (d.next h).map z = (d.star i).patchMap h z)
    (g : CairnsCircleGap) (hg : g.IsGapOf ((d.next h).contacts σ)) :
    (∃ i, openSegment ℝ (σ g.first) (σ g.last) ⊆ (d.star i).front ∩ a) ∧
    (∀ t : I, (d.next h).map ((1-(t : ℝ)) • σ g.first + (t : ℝ) • σ g.last) =
      (1-(t : ℝ)) • (h ⟨σ g.first,⟨g.first,rfl⟩⟩ : ℂ) +
        (t : ℝ) • (h ⟨σ g.last,⟨g.last,rfl⟩⟩ : ℂ)) := by
  obtain ⟨x,hx,hxg⟩ := hg.2.2
  have hxarc : x ∈ g.openArc := hxg ▸ mem_connectedComponentIn hx
  have hxold : x ∉ s.contacts σ := by
    intro hh
    exact hx (hT.symm ▸ Or.inl hh)
  let i : ResidualComponent (s.contacts σ) :=
    ⟨connectedComponentIn (s.contacts σ)ᶜ x,⟨x,hxold,rfl⟩⟩
  have hxi : x ∈ (d.gap i).closedArc := by
    have hxo : x ∈ (d.gap i).openArc := (d.gap_arc i).symm ▸ mem_connectedComponentIn hxold
    obtain ⟨θ,hθ,rfl⟩ := hxo
    exact ⟨θ,⟨hθ.1.le,hθ.2.le⟩,rfl⟩
  obtain ⟨v,hv,hxv,hch,haff⟩ := cairns_star_missing_contact_global_gap hσ (d.star i) h
    (hgeo i) _ (cairns_successor_contacts_on_gap hσ d h hgeo hT i) x hxi hx
  have hend := (cairns_gaps_equal_of_common_point _ g v hg hv x hxarc hxv).2
  have hchord : openSegment ℝ (σ g.first) (σ g.last) ⊆ (d.star i).front ∩ a := by
    rcases pair_eq_pair_iff.mp hend with ⟨hf,hl⟩ | ⟨hf,hl⟩
    · simpa only [hf,hl] using hch
    · simpa only [hf,hl,openSegment_symm] using hch
  refine ⟨⟨i,hchord⟩,?_⟩
  apply cairns_affine_chord_unordered_endpoints σ
    (fun t ↦ (h ⟨σ t,⟨t,rfl⟩⟩ : ℂ)) (d.next h).map g.first g.last v.first v.last hend
  intro t
  have hclosed : segment ℝ (σ v.first) (σ v.last) ⊆ closure (d.star i).sourceStar := by
    intro z hz
    have hopencl : openSegment ℝ (σ v.first) (σ v.last) ⊆ closure (d.star i).sourceStar := by
      intro w hw
      exact frontier_subset_closure ((hgeo i).2.2.2.1 ▸ Or.inr (hch hw).1)
    have hh := closure_mono hopencl (segment_subset_closure_openSegment hz)
    simpa only [closure_closure] using hh
  rw [hpatch i _ (hclosed ⟨1-t,t,sub_nonneg.mpr t.property.2,t.property.1,
    sub_add_cancel _ _,rfl⟩)]
  exact haff t

end HolomorphicAnosov.Topology.Plane

