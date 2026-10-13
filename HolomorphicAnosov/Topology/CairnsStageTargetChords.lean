import HolomorphicAnosov.Topology.CairnsStageGeometry
import HolomorphicAnosov.Topology.CairnsLiteralCarrierProperties
import HolomorphicAnosov.Topology.CairnsFrontierImage
import HolomorphicAnosov.Topology.CairnsSuccessorTargetImage

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- Each actual source gap gives a target frontier chord in the open unit
disk. The affine formula maps its source chord onto the target chord; the
compact carrier homeomorphism transports frontiers. Source: Cairns §4(C). -/
theorem cairns_stage_target_gap_chord
    {σ : Circle → ℂ} {a : Set ℂ} {s : Stage}
    (hab : Bornology.IsBounded a) (h : range σ ≃ₜ Circle) (hs : StageGeometry σ a h s)
    (g : CairnsCircleGap) (hg : g.IsGapOf (s.contacts σ)) :
    openSegment ℝ (h ⟨σ g.first,⟨g.first,rfl⟩⟩ : ℂ)
      (h ⟨σ g.last,⟨g.last,rfl⟩⟩ : ℂ) ⊆ frontier s.target := by
  obtain ⟨H,hH⟩ := hs.carrier
  obtain ⟨hc,hbij,hi⟩ := literal_carrier_homeomorph_properties _ _ s.map H hH
  have hf := compact_closure_frontier_image s.region s.map (hab.subset hs.subset).isCompact_closure
    (hc.mono subset_union_left) (hbij.injOn.mono subset_union_left) hs.isOpen hs.target_open
  rw [← affine_chord_image_openSegment _ _ _ _ _ (hs.affine g hg)]
  exact (image_mono ((hs.chord g hg).trans inter_subset_right)).trans hf.subset

end HolomorphicAnosov.Topology.Plane

