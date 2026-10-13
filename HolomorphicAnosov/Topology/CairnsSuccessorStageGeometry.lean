import HolomorphicAnosov.Topology.CairnsStageGeometry
import HolomorphicAnosov.Topology.CairnsSuccessorLiteralPatches
import HolomorphicAnosov.Topology.CairnsSuccessorContinuity
import HolomorphicAnosov.Topology.CairnsSuccessorTargetSeparation
import HolomorphicAnosov.Topology.CairnsSuccessorCarrierHomeomorph
import HolomorphicAnosov.Topology.CairnsSuccessorTargetClosure
import HolomorphicAnosov.Topology.CairnsSuccessorTargetOpen
import HolomorphicAnosov.Topology.CairnsSuccessorDiskOpenness
import HolomorphicAnosov.Topology.CairnsSuccessorFrontierUnion
import HolomorphicAnosov.Topology.CairnsSuccessorFrontierGaps
import HolomorphicAnosov.Topology.CairnsStageTargetFrontier
import HolomorphicAnosov.Topology.CairnsStageDiskCell
import HolomorphicAnosov.Topology.CairnsGapProperFrontierChord

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsStar CairnsRefinement

/-- The actual simultaneous outside-star successor preserves the complete
stage invariant. Null-family compactness identifies its closure, affine seam
compatibility glues its literal map, target supporting chords prevent cross
patch collisions, and disk-cell seam gluing gives source openness. Front
replacement identifies the new source frontier and its affine gap chords;
transport under the literal carrier map identifies the target frontier and
its convex contact hull. That convex hull supplies the next disk cell chart.
Source: Cairns §4(C), induction behind equations (4.3)–(4.4). -/
theorem cairns_successor_stage_geometry
    {σ : Circle → ℂ} {a : Set ℂ} {s : Stage}
    (hσ : Topology.IsEmbedding σ)
    (ha : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (hab : Bornology.IsBounded a) (h : range σ ≃ₜ Circle)
    (hs : StageGeometry σ a h s) (d : StepData σ a s)
    (hgeo : ∀ i, StarGeometry (d.star i) h) :
    StageGeometry σ a h (d.next h) := by
  classical
  let t := d.next h
  have hstar := fun i ↦ (hgeo i).2.2.1
  have hchord := fun i ↦ hs.chord (d.gap i) (d.gap_isGap i)
  have hseam : ∀ i, openSegment ℝ (σ (d.gap i).first) (σ (d.gap i).last) ⊆ closure s.region :=
    fun i ↦ (hchord i).trans (inter_subset_right.trans frontier_subset_closure)
  have hbase : ∀ i, segment ℝ (σ (d.gap i).first) (σ (d.gap i).last) ⊆ frontier s.region := by
    intro i z hz
    have hh := closure_mono ((hchord i).trans inter_subset_right) (segment_subset_closure_openSegment hz)
    simpa only [isClosed_frontier.closure_eq] using hh
  have hinter : ∀ i, closure s.region ∩ closure (d.star i).sourceStar =
      segment ℝ (σ (d.gap i).first) (σ (d.gap i).last) := by
    intro i
    apply cairns_successor_star_closure_intersection hσ ha d i (hstar i) _ (hseam i)
    intro z hz
    exact frontier_subset_closure ((hgeo i).2.2.2.1 ▸ Or.inl hz)
  have hpatch := cairns_successor_literal_patches hσ ha d h hgeo hs.curve hseam
    (fun i ↦ hs.affine _ (d.gap_isGap i))
  have hcompactUnion := cairns_successor_closed_stars_compact hσ ha hab d
    (hab.subset hs.subset) hstar
  have hcl := cairns_successor_region_closure (h := h) d hcompactUnion.isClosed hseam
  have hcompact : IsCompact (closure t.region) := hcl.symm ▸ hcompactUnion
  have hfullset : (closure s.region ∪ range σ) ∪ ⋃ i, closure (d.star i).sourceStar =
      closure t.region ∪ range σ := by
    rw [hcl]
    ext z
    simp only [mem_union]
    tauto
  have hfullcompact : IsCompact ((closure s.region ∪ range σ) ∪ ⋃ i, closure (d.star i).sourceStar) :=
    hfullset.symm ▸ hcompact.union (isCompact_range hσ.continuous)
  obtain ⟨H₀,hH₀⟩ := hs.carrier
  obtain ⟨hc₀,hbij₀,himage₀⟩ := literal_carrier_homeomorph_properties _ _ s.map H₀ hH₀
  have hfullcont := cairns_successor_continuousOn hσ ha hab (hab.subset hs.subset) d h hgeo hc₀ hs.curve hpatch
  have htcont : ContinuousOn t.map (closure t.region) := (hfullset ▸ hfullcont).mono subset_union_left
  have hT := cairns_successor_contacts d hcl (fun i ↦ (hgeo i).2.2.2.2.2.2.2.2.2.2.2.2.2.1)
  have hsub : t.region ⊆ a := by
    rintro z (hz | hz)
    · exact hs.subset hz
    · obtain ⟨i,hi | hi⟩ := mem_iUnion.mp hz
      · exact (cairns_star_sector_geometry hσ ha (d.star i)).2.2.2 (hstar i hi)
      · exact (hchord i hi).1
  have hcurveDis : Disjoint t.region (range σ) := by
    obtain ⟨x,hx,hxa⟩ := ha
    apply disjoint_left.mpr
    intro z hz hzc
    exact connectedComponentIn_subset (range σ)ᶜ x (hxa.symm ▸ hsub hz) hzc
  have hthree : ∃ p q r : Circle, p ∈ s.contacts σ ∧ q ∈ s.contacts σ ∧ r ∈ s.contacts σ ∧
      p ≠ q ∧ p ≠ r ∧ q ≠ r := by
    obtain ⟨p,q,r,u,hp,hq,hr,hu,hpq,hpr,hpu,hqr,hqu,hru⟩ := hs.four
    exact ⟨p,q,r,hp,hq,hr,hpq,hpr,hqr⟩
  have hopen := cairns_successor_open_of_disk_cell hσ ha d h hgeo hs.isOpen hs.cell
    (fun i ↦ (hchord i).trans inter_subset_left) hbase
    (fun i ↦ cairns_gap_proper_frontier_chord hσ ha hthree hs.isOpen hs.subset
      _ (d.gap_isGap i) ((hchord i).trans inter_subset_left)) hinter
  have hfrontbase : ∀ i, (d.star i).front ∩ segment ℝ (σ (d.gap i).first) (σ (d.gap i).last) ⊆ range σ := by
    intro i z hz
    rw [cairns_geometric_star_front_base_intersection hσ (d.star i) h (hgeo i)] at hz
    rcases hz with rfl | rfl <;> exact mem_range_self _
  have hfront := cairns_successor_frontier_union d h hgeo hs.isOpen hopen hcurveDis hcl
    (hs.source_frontier d.gap d.gap_isGap d.gap_arc) hseam hinter hfrontbase
    (cairns_successor_star_overlap_in_old_carrier hσ ha d hstar hseam)
  obtain ⟨htargetInter,htargetOverlap⟩ := cairns_successor_target_separation hσ d h hgeo hs.target_closure
  obtain ⟨H,hH⟩ := cairns_successor_carrier_homeomorph d h hgeo H₀ hH₀ hs.curve hpatch
    hfullcompact hfullcont hinter htargetInter htargetOverlap
  have htcl := cairns_successor_target_closure d h hgeo hpatch hcl hcompact htcont
    (image_closure_eq_of_compact_closure s.region s.map (hab.subset hs.subset).isCompact_closure
      (hc₀.mono subset_union_left))
  have hcodset : (closure s.target ∪ range (fun z : Circle ↦ (z : ℂ))) ∪
      ⋃ i, closure ((d.star i).targetStar h) = closure t.target ∪ range (fun z : Circle ↦ (z : ℂ)) := by
    rw [htcl]
    ext z
    simp only [mem_union]
    tauto
  let Ht := ((Homeomorph.setCongr hfullset).symm.trans H).trans (Homeomorph.setCongr hcodset)
  have hHt : ∀ x, (Ht x : ℂ) = t.map x := fun x ↦ hH ⟨x,hfullset.symm ▸ x.property⟩
  have htopen : IsOpen t.target :=
    cairns_target_open_of_carrier_homeomorph (s := t) (t := ⟨t.target,t.map⟩) Ht hHt hopen rfl
  have hne : t.region.Nonempty := hs.nonempty.mono subset_union_left
  have htne : t.target.Nonempty := hne.image _
  have hcurve : ∀ (z : ℂ) (hz : z ∈ range σ), t.map z = (h ⟨z,hz⟩ : ℂ) := by
    intro z hz
    change (if z ∈ closure s.region ∪ range σ then s.map z else _) = _
    have hmem : z ∈ closure s.region ∪ range σ := Or.inr hz
    rw [ite_eq_left hmem]
    exact hs.curve z hz
  have hfour : ∃ t₁ t₂ t₃ t₄ : Circle,
      t₁ ∈ t.contacts σ ∧ t₂ ∈ t.contacts σ ∧ t₃ ∈ t.contacts σ ∧ t₄ ∈ t.contacts σ ∧
      t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₁ ≠ t₄ ∧ t₂ ≠ t₃ ∧ t₂ ≠ t₄ ∧ t₃ ≠ t₄ := by
    obtain ⟨p,q,r,u,hp,hq,hr,hu,hneq⟩ := hs.four
    have hmono : s.contacts σ ⊆ t.contacts σ := hT.symm ▸ subset_union_left
    exact ⟨p,q,r,u,hmono hp,hmono hq,hmono hr,hmono hu,hneq⟩
  have hgapAff := fun g hg ↦ cairns_successor_gap_front_affine hσ d h hgeo hT hpatch g hg
  have hchordNew : ∀ g : CairnsCircleGap, g.IsGapOf (t.contacts σ) →
      openSegment ℝ (σ g.first) (σ g.last) ⊆ a ∩ frontier t.region := by
    intro g hg
    obtain ⟨i,hi⟩ := (hgapAff g hg).1
    intro z hz
    exact ⟨(hi hz).2,hfront.symm ▸ Or.inr (mem_iUnion.mpr ⟨i,(hi hz).1⟩)⟩
  have hfrontNew := cairns_successor_frontier_contact_chords hσ d h hgeo hT hpatch hfront hopen hcurveDis
  have htball : t.target ⊆ Metric.ball (0 : ℂ) 1 := by
    rw [cairns_successor_target_image d h hgeo hpatch hseam (fun i ↦ hs.affine _ (d.gap_isGap i))]
    apply union_subset hs.target_ball
    apply iUnion_subset
    intro i
    obtain ⟨Hi,hHi,hi,hb,hn,ho,hball,hrest⟩ := cairns_geometric_star_literal_extension (d.star i) h (hgeo i)
    apply union_subset hball
    have hp : (h ⟨σ (d.gap i).first,⟨(d.gap i).first,rfl⟩⟩ : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
      simp only [Metric.mem_closedBall,dist_zero_right,Circle.norm_coe,le_refl]
    have hq : (h ⟨σ (d.gap i).last,⟨(d.gap i).last,rfl⟩⟩ : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
      simp only [Metric.mem_closedBall,dist_zero_right,Circle.norm_coe,le_refl]
    apply openSegment_subset_ball_of_ne hp hq
    intro he
    have he' := hσ.injective (congrArg Subtype.val (h.injective (Subtype.ext he)))
    exact (d.gap i).start_lt_stop.ne (Circle.exp_injOn_Icc (d.gap i).shorter_than_turn
      ⟨le_rfl,(d.gap i).start_lt_stop.le⟩ ⟨(d.gap i).start_lt_stop.le,le_rfl⟩ he')
  have hTclosed : IsClosed (t.contacts σ) := isClosed_closure.preimage hσ.continuous
  choose gap hgap harc using cairns_gap_of_residual_component _ hTclosed hfour
  have hTne : (t.contacts σ).Nonempty := by
    obtain ⟨p,q,r,u,hp,hrest⟩ := hfour
    exact ⟨p,hp⟩
  have hbij := (literal_carrier_homeomorph_properties _ _ t.map Ht hHt).2.1
  have htargetfront := cairns_stage_target_frontier t h hcompact htcont
    (hbij.injOn.mono subset_union_left) hopen htopen hcurve gap (hfrontNew gap hgap harc)
    (fun i ↦ (hgapAff _ (hgap i)).2)
  obtain ⟨hhull,hthull,htconvex,htdisk,htcircle⟩ := cairns_stage_target_contact_hull hσ t h htne htopen htball
    hTclosed hTne gap hgap htargetfront
  obtain ⟨hconn,hcell⟩ := cairns_stage_disk_cell t hopen htopen htne htconvex
    ((Metric.isBounded_ball (x := (0 : ℂ)) (r := 1)).subset htball) Ht hHt
  exact ⟨hne,hopen,hsub,hconn,hfour,hcurve,hchordNew,(fun g hg ↦ (hgapAff g hg).2),
    hfrontNew,htne,htopen,htball,htconvex,hthull,⟨Ht,hHt⟩,hcell⟩

end HolomorphicAnosov.Topology.Plane

