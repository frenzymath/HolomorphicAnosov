import HolomorphicAnosov.Topology.CairnsTargetSectorLocalOpen
import HolomorphicAnosov.Topology.CairnsTargetSectorFamily
import HolomorphicAnosov.Topology.CairnsStageTargetFrontier
import HolomorphicAnosov.Topology.CairnsLiteralCarrierProperties

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- The circular caps selected for the actual gap labels exhaust the target
disk outside the old target closure. Their closed union with the old closure
is compact by the null-family arc diameter estimate. Adjoin each open chord:
local disk-cell gluing makes the union open. Its boundary inside the disk is
empty by the old contact/chord frontier formula and the cap frontier bounds.
Connectedness of the disk forces the union to be the whole disk. Source:
Cairns §4(C), target residual-sector partition. -/
theorem cairns_target_sectors_cover
    {σ : Circle → ℂ} {a : Set ℂ} {s : Stage}
    (hσ : Topology.IsEmbedding σ) (hab : Bornology.IsBounded a)
    (h : range σ ≃ₜ Circle) (hs : StageGeometry σ a h s) (d : StepData σ a s)
    (b : ∀ i, StarChoice (fun t : Circle ↦ (h ⟨σ t,⟨t,rfl⟩⟩ : ℂ))
      (Metric.ball (0 : ℂ) 1) (d.gap i))
    (hout : ∀ i, Disjoint (b i).sector s.target) :
    Metric.ball (0 : ℂ) 1 \ closure s.target = ⋃ i, (b i).sector := by
  let τ := fun t : Circle ↦ (h ⟨σ t,⟨t,rfl⟩⟩ : ℂ)
  let C := closure s.target ∪ ⋃ i, closure (b i).sector
  let W := s.target ∪ ⋃ i, (s.target ∪ (b i).sector ∪
    openSegment ℝ (τ (d.gap i).first) (τ (d.gap i).last))
  obtain ⟨hτ,hτrange,hcomponent⟩ := cairns_target_boundary_geometry hσ h
  have hcontacts : τ ⁻¹' closure s.target = s.contacts σ := cairns_target_stage_contacts h hs
  have hgeometry := fun i ↦ cairns_star_sector_geometry hτ hcomponent (b i)
  have hchord := fun i ↦ cairns_stage_target_gap_chord hab h hs (d.gap i) (d.gap_isGap i)
  have hseam : ∀ i, openSegment ℝ (τ (d.gap i).first) (τ (d.gap i).last) ⊆
      closure s.target := fun i ↦ (hchord i).trans frontier_subset_closure
  have hCcompact : IsCompact C := by
    let size := fun i ↦ Metric.diam (τ '' (d.gap i).closedArc)
    apply null_patch_union_isCompact (closure s.target)
      (Metric.isBounded_ball.subset hs.target_ball).isCompact_closure
      (fun i ↦ closure (b i).sector)
      (fun i ↦ (Metric.isBounded_ball.subset (hgeometry i).2.2.2).isCompact_closure)
      (fun i ↦ τ (d.gap i).first)
      (fun i ↦ show τ (d.gap i).first ∈ closure s.target from
        (show (d.gap i).first ∈ τ ⁻¹' closure s.target from hcontacts ▸ (d.gap_isGap i).1)) size
    · intro i z hz
      have hfirst : (d.gap i).first ∈ (d.gap i).closedArc :=
        ⟨(d.gap i).start,⟨le_rfl,(d.gap i).start_lt_stop.le⟩,rfl⟩
      have hbounded : Bornology.IsBounded (τ '' (d.gap i).closedArc) :=
        (isCompact_range hτ.continuous).isBounded.subset (image_subset_range _ _)
      have harc : τ '' (d.gap i).closedArc ⊆ Metric.closedBall (τ (d.gap i).first) (size i) :=
        fun y hy ↦ Metric.dist_le_diam_of_mem hbounded hy (mem_image_of_mem τ hfirst)
      exact cairns_star_sector_closure_subset_closedBall hτ hcomponent Metric.isBounded_ball
        (b i) _ _ harc hz
    · intro j hj
      exact CairnsCircleGap.image_diam_tendsto_zero_of_disjoint τ hτ.continuous d.gap
        (cairns_step_gap_pairwise_disjoint d) j hj
  have hWopen : IsOpen W := hs.target_open.union (isOpen_iUnion (fun i ↦
    cairns_target_sector_local_open hσ hab h hs (d.gap i) (d.gap_isGap i) (b i) (hout i)))
  have hWC : W ⊆ C := by
    rintro z (hz | hz)
    · exact Or.inl (subset_closure hz)
    · obtain ⟨i,(hi | hi) | hi⟩ := mem_iUnion.mp hz
      · exact Or.inl (subset_closure hi)
      · exact Or.inr (mem_iUnion.mpr ⟨i,subset_closure hi⟩)
      · exact Or.inl (hseam i hi)
  have hnotcurve : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ∉ range τ := by
    rintro z hz ⟨t,rfl⟩
    have ht : τ t ∈ Metric.sphere (0 : ℂ) 1 := by simp [τ]
    exact (Metric.mem_ball.mp hz).ne (Metric.mem_sphere.mp ht)
  obtain ⟨H,hH⟩ := hs.carrier
  obtain ⟨hcont,hbij,hi⟩ := literal_carrier_homeomorph_properties _ _ s.map H hH
  have hfront := cairns_stage_target_frontier s h (hab.subset hs.subset).isCompact_closure
    (hcont.mono subset_union_left) (hbij.injOn.mono subset_union_left) hs.isOpen hs.target_open
    hs.curve d.gap (hs.source_frontier d.gap d.gap_isGap d.gap_arc)
    (fun i ↦ hs.affine (d.gap i) (d.gap_isGap i))
  have hCW : C ∩ Metric.ball (0 : ℂ) 1 ⊆ W := by
    rintro z ⟨hz,hza⟩
    rcases hz with hzold | hzsector
    · by_cases hzreg : z ∈ s.target
      · exact Or.inl hzreg
      · have hzf : z ∈ frontier s.target := by
          rw [hs.target_open.frontier_eq]
          exact ⟨hzold,hzreg⟩
        rw [hfront] at hzf
        rcases hzf with hzc | hzch
        · exact (hnotcurve z hza (image_subset_range _ _ hzc)).elim
        · obtain ⟨i,hi⟩ := mem_iUnion.mp hzch
          exact Or.inr (mem_iUnion.mpr ⟨i,Or.inr hi⟩)
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hzsector
      by_cases hzsec : z ∈ (b i).sector
      · exact Or.inr (mem_iUnion.mpr ⟨i,Or.inl (Or.inr hzsec)⟩)
      · have hzf : z ∈ frontier (b i).sector := by
          rw [(hgeometry i).2.1.frontier_eq]
          exact ⟨hi,hzsec⟩
        rcases (b i).frontier_subset hzf with hzbase | hzarc
        · have hn₁ : τ (d.gap i).first ≠ z := fun he ↦ hnotcurve z hza (he ▸ mem_range_self _)
          have hn₂ : τ (d.gap i).last ≠ z := fun he ↦ hnotcurve z hza (he ▸ mem_range_self _)
          exact Or.inr (mem_iUnion.mpr ⟨i,Or.inr
            (mem_openSegment_of_ne_left_right hn₁ hn₂ hzbase)⟩)
        · exact (hnotcurve z hza (image_subset_range _ _ hzarc)).elim
  have hballW : Metric.ball (0 : ℂ) 1 ⊆ W := by
    apply (convex_ball (0 : ℂ) 1).isPreconnected.subset_of_closure_inter_subset hWopen
    · obtain ⟨z,hz⟩ := hs.target_nonempty
      exact ⟨z,hs.target_ball hz,Or.inl hz⟩
    · exact fun z hz ↦ hCW ⟨closure_minimal hWC hCcompact.isClosed hz.1,hz.2⟩
  apply Subset.antisymm
  · rintro z ⟨hza,hznot⟩
    rcases hballW hza with hz | hz
    · exact (hznot (subset_closure hz)).elim
    · obtain ⟨i,(hi | hi) | hi⟩ := mem_iUnion.mp hz
      · exact (hznot (subset_closure hi)).elim
      · exact mem_iUnion.mpr ⟨i,hi⟩
      · exact (hznot (hseam i hi)).elim
  · intro z hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    exact ⟨(hgeometry i).2.2.2 hi,fun hzcl ↦
      disjoint_left.mp ((hout i).closure_right (hgeometry i).2.1) hi hzcl⟩

end HolomorphicAnosov.Topology.Plane

