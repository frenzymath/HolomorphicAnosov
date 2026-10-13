import HolomorphicAnosov.Topology.CairnsSuccessorCompactness
import HolomorphicAnosov.Topology.CairnsStageGeometry

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- The old closed region and all closed outside sectors form a compact null
union. Every sector is confined by its original closed gap arc, and its first
endpoint is an anchor in the old closure. Distinct gap arc diameters tend to
zero. Source: Cairns §4(C), residual sector accumulation. -/
theorem cairns_closed_sectors_compact
    {σ : Circle → ℂ} {a : Set ℂ} {s : Stage}
    (hσ : Topology.IsEmbedding σ)
    (ha : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (haBounded : Bornology.IsBounded a) (d : StepData σ a s)
    (hs : Bornology.IsBounded s.region) :
    IsCompact (closure s.region ∪ ⋃ i, closure (d.star i).sector) := by
  let size := fun i ↦ Metric.diam (σ '' (d.gap i).closedArc)
  have hbounded (i) : Bornology.IsBounded (d.star i).sector :=
    haBounded.subset (cairns_star_sector_geometry hσ ha (d.star i)).2.2.2
  apply null_patch_union_isCompact (closure s.region) hs.isCompact_closure
    (fun i ↦ closure (d.star i).sector) (fun i ↦ (hbounded i).isCompact_closure)
    (fun i ↦ σ (d.gap i).first) (fun i ↦ (d.gap_isGap i).1) size
  · intro i z hz
    have hfirst : (d.gap i).first ∈ (d.gap i).closedArc :=
      ⟨(d.gap i).start, ⟨le_rfl,(d.gap i).start_lt_stop.le⟩,rfl⟩
    have hcb : Bornology.IsBounded (σ '' (d.gap i).closedArc) := by
      apply Bornology.IsBounded.subset (isCompact_range hσ.continuous).isBounded
      exact image_subset_range _ _
    have harc : σ '' (d.gap i).closedArc ⊆
        Metric.closedBall (σ (d.gap i).first) (size i) := by
      intro y hy
      exact Metric.dist_le_diam_of_mem hcb hy (mem_image_of_mem σ hfirst)
    exact cairns_star_sector_closure_subset_closedBall hσ ha haBounded
      (d.star i) _ _ harc hz
  · intro j hj
    exact CairnsCircleGap.image_diam_tendsto_zero_of_disjoint σ hσ.continuous d.gap
      (cairns_step_gap_pairwise_disjoint d) j hj


/-- The chosen outside sectors exhaust the residual original region. Adjoin
them to the open successor: this union is open, while its closure inside the
original component stays in the same union by the old frontier formula and
the sector frontier bounds. Null-family compactness controls accumulation.
Connectedness forces this nonempty open and relatively closed union to be the
whole original region; removing the old closure leaves exactly its sectors.
Source: Cairns §4(C), residual-sector partition. -/
theorem cairns_residual_sectors_cover
    {σ : Circle → ℂ} {a : Set ℂ} {s : Stage}
    (hσ : Topology.IsEmbedding σ)
    (ha : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (hab : Bornology.IsBounded a) (d : StepData σ a s) (h : range σ ≃ₜ Circle)
    (hs : StageGeometry σ a h s) (hnextopen : IsOpen (d.next h).region)
    (hstar : ∀ i, (d.star i).sourceStar ⊆ (d.star i).sector) :
    a \ closure s.region = ⋃ i, (d.star i).sector := by
  let C := closure s.region ∪ ⋃ i, closure (d.star i).sector
  let W := (d.next h).region ∪ ⋃ i, (d.star i).sector
  have hCcompact : IsCompact C := cairns_closed_sectors_compact hσ ha hab d (hab.subset hs.subset)
  have hseam : ∀ i, openSegment ℝ (σ (d.gap i).first) (σ (d.gap i).last) ⊆ closure s.region :=
    fun i ↦ (hs.chord _ (d.gap_isGap i)).trans (inter_subset_right.trans frontier_subset_closure)
  have hsector := fun i ↦ cairns_star_sector_geometry hσ ha (d.star i)
  have hWopen : IsOpen W := hnextopen.union (isOpen_iUnion (fun i ↦ (hsector i).2.1))
  have hWC : W ⊆ C := by
    rintro z ((hz | hz) | hz)
    · exact Or.inl (subset_closure hz)
    · obtain ⟨i,hi | hi⟩ := mem_iUnion.mp hz
      · exact Or.inr (mem_iUnion.mpr ⟨i,subset_closure (hstar i hi)⟩)
      · exact Or.inl (hseam i hi)
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hz
      exact Or.inr (mem_iUnion.mpr ⟨i,subset_closure hi⟩)
  obtain ⟨x,hx,hxa⟩ := ha
  have hac : a ⊆ (range σ)ᶜ := hxa ▸ connectedComponentIn_subset (range σ)ᶜ x
  have hCW : C ∩ a ⊆ W := by
    rintro z ⟨hz,hza⟩
    rcases hz with hzold | hzsector
    · by_cases hzreg : z ∈ s.region
      · exact Or.inl (Or.inl hzreg)
      · have hzf : z ∈ frontier s.region := by
          rw [hs.isOpen.frontier_eq]
          exact ⟨hzold,hzreg⟩
        rw [hs.source_frontier d.gap d.gap_isGap d.gap_arc] at hzf
        rcases hzf with hzc | hzch
        · exact (hac hza (image_subset_range _ _ hzc)).elim
        · obtain ⟨i,hi⟩ := mem_iUnion.mp hzch
          exact Or.inl (Or.inr (mem_iUnion.mpr ⟨i,Or.inr hi⟩))
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hzsector
      by_cases hzsec : z ∈ (d.star i).sector
      · exact Or.inr (mem_iUnion.mpr ⟨i,hzsec⟩)
      · have hzf : z ∈ frontier (d.star i).sector := by
          rw [(hsector i).2.1.frontier_eq]
          exact ⟨hi,hzsec⟩
        rcases (d.star i).frontier_subset hzf with hzbase | hzarc
        · have hn₁ : σ (d.gap i).first ≠ z := fun he ↦ hac hza (he ▸ mem_range_self _)
          have hn₂ : σ (d.gap i).last ≠ z := fun he ↦ hac hza (he ▸ mem_range_self _)
          exact Or.inl (Or.inr (mem_iUnion.mpr ⟨i,Or.inr
            (mem_openSegment_of_ne_left_right hn₁ hn₂ hzbase)⟩))
        · exact (hac hza (image_subset_range _ _ hzarc)).elim
  have haW : a ⊆ W := by
    have haconn : IsPreconnected a := hxa ▸ isPreconnected_connectedComponentIn
    apply haconn.subset_of_closure_inter_subset hWopen
    · obtain ⟨z,hz⟩ := hs.nonempty
      exact ⟨z,hs.subset hz,Or.inl (Or.inl hz)⟩
    · exact fun z hz ↦ hCW ⟨closure_minimal hWC hCcompact.isClosed hz.1,hz.2⟩
  apply Subset.antisymm
  · rintro z ⟨hza,hznot⟩
    rcases haW hza with hz | hz
    · rcases hz with hzold | hznew
      · exact (hznot (subset_closure hzold)).elim
      · obtain ⟨i,hi | hi⟩ := mem_iUnion.mp hznew
        · exact mem_iUnion.mpr ⟨i,hstar i hi⟩
        · exact (hznot (hseam i hi)).elim
    · exact hz
  · intro z hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    exact ⟨(hsector i).2.2.2 hi,fun hzcl ↦
      disjoint_left.mp ((d.outside i).closure_right (hsector i).2.1) hi hzcl⟩

end HolomorphicAnosov.Topology.Plane

