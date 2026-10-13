import HolomorphicAnosov.Topology.CairnsResidualComponentGap
import HolomorphicAnosov.Topology.CairnsStageGeometry
import HolomorphicAnosov.Topology.CairnsInitialContactsFour
import HolomorphicAnosov.Topology.CairnsInitialGapAffine
import HolomorphicAnosov.Topology.CairnsInitialTargetRegion
import HolomorphicAnosov.Topology.CairnsStageTargetFrontier
import HolomorphicAnosov.Topology.CairnsStageDiskCell

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- The two opposite geometric initial stars satisfy the complete stage
invariant. Two-cell gluing supplies the open region, literal patch pasting
supplies its map and target, and the four actual first contacts label all
remaining gaps. Their affine front chords identify the target contact hull;
its convex disk chart transports to the initial source cell. Source: Cairns
§4(B), initialization of the recurrence. -/
theorem cairns_initial_stage_geometry
    {σ : Circle → ℂ} {a : Set ℂ} {p q : Circle}
    (hσ : Topology.IsEmbedding σ)
    (ha : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (hab : Bornology.IsBounded a) (h : range σ ≃ₜ Circle)
    (hpq : p ≠ q) (d : InitialData σ a p q)
    (hchord : openSegment ℝ (σ p) (σ q) ⊆ a)
    (h₁ : StarGeometry d.firstStar h) (h₂ : StarGeometry d.secondStar h)
    (hop₁ : IsOpen d.firstStar.sector) (hop₂ : IsOpen d.secondStar.sector)
    (hdisj : Disjoint d.firstStar.sector d.secondStar.sector) :
    StageGeometry σ a h (d.stage h) := by
  classical
  let s := d.stage h
  obtain ⟨hne,hopen,hsub,hdisk,hcircle,hfront,hcl,hinter⟩ :=
    cairns_initial_region_cell hσ ha h d hchord h₁ h₂ hop₁ hop₂ hdisj
  obtain ⟨htne,htopen,htball,htimage,htcl,H,hH⟩ :=
    cairns_initial_target_region hσ ha hab h d hchord h₁ h₂ hop₁ hop₂ hdisj
  obtain ⟨H',hH',hmap₁,hmap₂⟩ := cairns_initial_literal_homeomorph hσ ha hab h d h₁ h₂ hinter
  have hfour := cairns_initial_contacts_four (h := h) hpq d
  have hcurve : ∀ (z : ℂ) (hz : z ∈ range σ), s.map z = (h ⟨z,hz⟩ : ℂ) := by
    intro z hz
    simp only [s,InitialData.stage,dite_eq_left hz]
  have hchordAll : ∀ g : CairnsCircleGap, g.IsGapOf (s.contacts σ) →
      openSegment ℝ (σ g.first) (σ g.last) ⊆ a ∩ frontier s.region := by
    intro g hg z hz
    exact (cairns_initial_gap_chord_frontier hσ h d h₁ h₂ hcl hfront g hg hz).symm
  have haff := cairns_initial_map_gap_affine hσ h d h₁ h₂ hcl hmap₁ hmap₂
  have hfrontAll := cairns_initial_frontier_contact_chords hσ ha h d h₁ h₂ hcl hfront hopen hsub
  have hTclosed : IsClosed (s.contacts σ) := isClosed_closure.preimage hσ.continuous
  choose gap hgap harc using cairns_gap_of_residual_component _ hTclosed hfour
  have hTne : (s.contacts σ).Nonempty := by
    obtain ⟨u,v,w,x,hu,hrest⟩ := hfour
    exact ⟨u,hu⟩
  obtain ⟨hc,hbij,hi⟩ := literal_carrier_homeomorph_properties _ _ s.map H hH
  have htargetfront := cairns_stage_target_frontier s h (hab.subset hsub).isCompact_closure
    (hc.mono subset_union_left) (hbij.injOn.mono subset_union_left) hopen htopen hcurve
    gap (hfrontAll gap hgap harc) (fun i ↦ haff _ (hgap i))
  obtain ⟨hhull,hthull,htconvex,htdisk,htcircle⟩ := cairns_stage_target_contact_hull hσ s h
    htne htopen htball hTclosed hTne gap hgap htargetfront
  obtain ⟨hconn,hcell⟩ := cairns_stage_disk_cell s hopen htopen htne htconvex
    ((Metric.isBounded_ball (x := (0 : ℂ)) (r := 1)).subset htball) H hH
  exact ⟨hne,hopen,hsub,hconn,hfour,hcurve,hchordAll,haff,hfrontAll,htne,htopen,htball,htconvex,
    hthull,⟨H,hH⟩,hcell⟩

end HolomorphicAnosov.Topology.Plane

