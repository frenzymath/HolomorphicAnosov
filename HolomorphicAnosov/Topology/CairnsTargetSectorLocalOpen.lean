import HolomorphicAnosov.Topology.CairnsTargetSectorHull
import HolomorphicAnosov.Topology.CairnsGapHullSeparation
import HolomorphicAnosov.Topology.CairnsDiskCellsOpenChord
import HolomorphicAnosov.Topology.CairnsClosedCellRestriction
import HolomorphicAnosov.Topology.CairnsGapProperFrontierChord
import HolomorphicAnosov.Topology.CairnsTargetBoundaryContacts
import HolomorphicAnosov.Topology.CairnsStageTargetChords

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- A bounded nonempty open convex plane set has a closed-disk cell chart
with its interior and frontier matched. This specializes the convex gauge
chart to the identity carrier. -/
theorem cairns_open_convex_disk_cell (U : Set ℂ) (ho : IsOpen U)
    (hn : U.Nonempty) (hc : Convex ℝ U) (hb : Bornology.IsBounded U) :
    ∃ G : closure U ≃ₜ Metric.closedBall (0 : ℂ) 1,
      G '' {z : closure U | (z : ℂ) ∈ U} =
        {w : Metric.closedBall (0 : ℂ) 1 | (w : ℂ) ∈ Metric.ball (0 : ℂ) 1} ∧
      G '' {z : closure U | (z : ℂ) ∈ frontier U} =
        {w : Metric.closedBall (0 : ℂ) 1 | (w : ℂ) ∈ Metric.sphere (0 : ℂ) 1} := by
  obtain ⟨G,hi,hf⟩ := carrier_homeomorph_closed_disk_chart (closure U) (closure U) U U
    ho ho hn hc hb subset_rfl subset_rfl (Homeomorph.refl _) (fun x ↦ Iff.rfl)
  have himage (P Q : Set ℂ)
      (hPQ : ∀ x : closure U, (x : ℂ) ∈ P ↔ (G x : ℂ) ∈ Q) :
      G '' {x : closure U | (x : ℂ) ∈ P} =
        {y : Metric.closedBall (0 : ℂ) 1 | (y : ℂ) ∈ Q} := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact (hPQ x).mp hx
    · intro hy
      refine ⟨G.symm y,(hPQ (G.symm y)).mpr ?_,G.apply_symm_apply y⟩
      simpa only [G.apply_symm_apply] using (show (y : ℂ) ∈ Q from hy)
  exact ⟨G,himage _ _ hi,himage _ _ hf⟩

/-- A target region and the outside circular cap fill a neighborhood of their
common open chord. Both are convex disk cells, their closed intersection is
exactly that chord, and retained circle contacts make it a proper boundary
arc on each side. Apply the two-disk-cell gluing theorem. Source: Cairns §4(C). -/
theorem cairns_target_sector_local_open
    {σ : Circle → ℂ} {a : Set ℂ} {s : Stage}
    (hσ : Topology.IsEmbedding σ) (hab : Bornology.IsBounded a)
    (h : range σ ≃ₜ Circle) (hs : StageGeometry σ a h s)
    (g : CairnsCircleGap) (hg : g.IsGapOf (s.contacts σ))
    (b : StarChoice (fun t : Circle ↦ (h ⟨σ t,⟨t,rfl⟩⟩ : ℂ)) (Metric.ball (0 : ℂ) 1) g)
    (hout : Disjoint b.sector s.target) :
    IsOpen (s.target ∪ b.sector ∪ openSegment ℝ
      (h ⟨σ g.first,⟨g.first,rfl⟩⟩ : ℂ) (h ⟨σ g.last,⟨g.last,rfl⟩⟩ : ℂ)) := by
  let τ := fun t : Circle ↦ (h ⟨σ t,⟨t,rfl⟩⟩ : ℂ)
  obtain ⟨hτ,hτrange,hcomponent⟩ := cairns_target_boundary_geometry hσ h
  have hnorm : ∀ t, ‖τ t‖ = 1 := fun t ↦ Circle.norm_coe _
  have hsphere (t : Circle) : τ t ∈ Metric.sphere (0 : ℂ) 1 := by simpa using hnorm t
  have hsurj : ∀ z : ℂ, ‖z‖ = 1 → ∃ t, τ t = z := by
    intro z hz
    let e : Circle ≃ₜ Circle := hσ.toHomeomorph.trans h
    let zc : Circle := ⟨z,mem_sphere_zero_iff_norm.mpr hz⟩
    exact ⟨e.symm zc,congrArg Subtype.val (e.apply_symm_apply zc)⟩
  have hne : g.first ≠ g.last := by
    intro he
    exact g.start_lt_stop.ne (Circle.exp_injOn_Icc g.shorter_than_turn
      ⟨le_rfl,g.start_lt_stop.le⟩ ⟨g.start_lt_stop.le,le_rfl⟩ he)
  have hchord : openSegment ℝ (τ g.first) (τ g.last) ⊆ Metric.ball (0 : ℂ) 1 :=
    openSegment_subset_ball_of_ne (Metric.sphere_subset_closedBall (hsphere _))
      (Metric.sphere_subset_closedBall (hsphere _)) (hτ.injective.ne hne)
  have hfront := cairns_stage_target_gap_chord hab h hs g hg
  have hbase : segment ℝ (τ g.first) (τ g.last) ⊆ frontier s.target := by
    intro z hz
    exact isClosed_frontier.closure_subset_iff.mpr hfront
      (segment_subset_closure_openSegment hz)
  have hfirst : g.first ∈ g.closedArc := ⟨g.start,⟨le_rfl,g.start_lt_stop.le⟩,rfl⟩
  have hlast : g.last ∈ g.closedArc := ⟨g.stop,⟨g.start_lt_stop.le,le_rfl⟩,rfl⟩
  obtain ⟨heq,hcl,hconvex⟩ := cairns_target_sector_hull τ hτ hnorm hcomponent g b
  obtain ⟨hbne,hbopen,hbconn,hbsub⟩ := cairns_star_sector_geometry hτ hcomponent b
  have hinter : closure b.sector ∩ closure s.target = segment ℝ (τ g.first) (τ g.last) := by
    rw [hcl,hs.target_closure]
    exact cairns_gap_hull_inter_contact_hull τ hτ.continuous hτ.injective hnorm hsurj
      (s.contacts σ) g hg g.closedArc subset_rfl hfirst hlast
  have hbbase : segment ℝ (τ g.first) (τ g.last) ⊆ frontier b.sector := by
    intro z hz
    rw [hbopen.frontier_eq]
    have hh : z ∈ closure b.sector ∩ closure s.target := hinter.symm ▸ hz
    exact ⟨hh.1,fun hzb ↦ disjoint_left.mp (hout.closure_right hbopen) hzb hh.2⟩
  have hcontacts : τ ⁻¹' closure s.target = s.contacts σ := cairns_target_stage_contacts h hs
  have hthree : ∃ p q r : Circle,
      p ∈ τ ⁻¹' closure s.target ∧ q ∈ τ ⁻¹' closure s.target ∧
      r ∈ τ ⁻¹' closure s.target ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r := by
    rw [hcontacts]
    obtain ⟨p,q,r,t,hp,hq,hr,_,hpq,hpr,_,hqr,_,_⟩ := hs.four
    exact ⟨p,q,r,hp,hq,hr,hpq,hpr,hqr⟩
  have hproper : segment ℝ (τ g.first) (τ g.last) ≠ frontier s.target :=
    cairns_gap_proper_frontier_chord (s := {region := s.target,map := id}) hτ hcomponent
      hthree hs.target_open hs.target_ball g (by change g.IsGapOf (τ ⁻¹' closure s.target); rw [hcontacts]; exact hg) hchord
  have hbproper : segment ℝ (τ g.first) (τ g.last) ≠ frontier b.sector := by
    let t := g.parameter b.contactParameter
    have ht : t ∈ g.openArc := by
      refine ⟨g.start + (g.stop-g.start) * (b.contactParameter : ℝ),?_,rfl⟩
      constructor <;> nlinarith [g.start_lt_stop,b.contact_pos,b.contact_lt_one]
    have htclosed : t ∈ g.closedArc := by
      obtain ⟨v,hv,he⟩ := ht
      exact ⟨v,⟨hv.1.le,hv.2.le⟩,he⟩
    have htne : t ≠ g.first ∧ t ≠ g.last := by
      obtain ⟨v,hv,hvt⟩ := ht
      rw [← hvt]
      exact ⟨fun he ↦ hv.1.ne' (Circle.exp_injOn_Icc g.shorter_than_turn
        ⟨hv.1.le,hv.2.le⟩ ⟨le_rfl,g.start_lt_stop.le⟩ he),
        fun he ↦ hv.2.ne (Circle.exp_injOn_Icc g.shorter_than_turn
        ⟨hv.1.le,hv.2.le⟩ ⟨g.start_lt_stop.le,le_rfl⟩ he)⟩
    have htnot : τ t ∉ Metric.ball (0 : ℂ) 1 :=
      fun hh ↦ (Metric.mem_ball.mp hh).ne (Metric.mem_sphere.mp (hsphere t))
    have htf : τ t ∈ frontier b.sector := by
      rw [hbopen.frontier_eq]
      exact ⟨hcl.symm ▸ subset_convexHull ℝ _ (mem_image_of_mem τ htclosed),
        fun hh ↦ htnot (hbsub hh)⟩
    intro he
    have htseg := he.symm ▸ htf
    exact htnot (hchord (mem_openSegment_of_ne_left_right
      (fun he ↦ htne.1 (hτ.injective he.symm))
      (fun he ↦ htne.2 (hτ.injective he.symm)) htseg))
  apply cairns_disk_cells_open_along_chord _ _ _ _ (hτ.injective.ne hne) _ hbase hbbase
    hproper hbproper (by rw [inter_comm]; exact hinter)
  intro W hW
  rcases hW with rfl | rfl
  · exact cairns_open_convex_disk_cell _ hs.target_open hs.target_nonempty hs.target_convex
      (Metric.isBounded_ball.subset hs.target_ball)
  · exact cairns_open_convex_disk_cell _ hbopen hbne hconvex (Metric.isBounded_ball.subset hbsub)

end HolomorphicAnosov.Topology.Plane

