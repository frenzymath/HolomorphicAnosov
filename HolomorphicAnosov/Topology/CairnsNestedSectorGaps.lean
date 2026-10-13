import HolomorphicAnosov.Topology.CairnsSuccessorSectorDisjoint
import HolomorphicAnosov.Topology.CairnsStageGeometry

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- When a later outside sector meets an earlier outside sector, it is
contained in the earlier component. Its first contact identifies the containing
old angular gap; component monotonicity then nests the entire open parameter
arc, and closure adds its endpoints. Source: Cairns §4(C), nested residual gaps. -/
theorem cairns_nested_sector_gap
    {σ : Circle → ℂ} {a : Set ℂ} {s t : Stage}
    (hσ : Topology.IsEmbedding σ)
    (ha : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (d : StepData σ a s) (e : StepData σ a t)
    (hmono : s.region ⊆ t.region)
    (hd : ∀ i, openSegment ℝ (σ (d.gap i).first) (σ (d.gap i).last) ⊆ closure s.region)
    (he : ∀ i, openSegment ℝ (σ (e.gap i).first) (σ (e.gap i).last) ⊆ closure t.region)
    (hstar : ∀ i, (e.star i).sourceStar ⊆ (e.star i).sector)
    (i : ResidualComponent (s.contacts σ)) (k : ResidualComponent (t.contacts σ))
    (hmeet : ((e.star k).sector ∩ (d.star i).sector).Nonempty) :
    (e.star k).sector ⊆ (d.star i).sector ∧ (e.gap k).closedArc ⊆ (d.gap i).closedArc := by
  obtain ⟨x,hx,hxi⟩ := cairns_star_sector_component_outside_closure
    hσ ha (d.star i) s.region (d.outside i) (hd i)
  obtain ⟨y,hy,hyk⟩ := cairns_star_sector_component_outside_closure
    hσ ha (e.star k) t.region (e.outside k) (he k)
  obtain ⟨z,hzk,hzi⟩ := hmeet
  have hsub : (e.star k).sector ⊆ (d.star i).sector := by
    have hzin : z ∈ connectedComponentIn (a \ closure s.region) x := hxi.symm ▸ hzi
    rw [← hxi,connectedComponentIn_eq hzin]
    apply (cairns_star_sector_geometry hσ ha (e.star k)).2.2.1.isPreconnected.subset_connectedComponentIn hzk
    intro w hw
    have hwsmall : w ∈ a \ closure t.region := by
      rw [← hyk] at hw
      exact connectedComponentIn_subset _ _ hw
    exact ⟨hwsmall.1,fun hh ↦ hwsmall.2 (closure_mono hmono hh)⟩
  let u := (e.gap k).parameter (e.star k).contactParameter
  have hu : u ∈ (e.gap k).openArc := by
    refine ⟨(e.gap k).start + ((e.gap k).stop-(e.gap k).start) *
      ((e.star k).contactParameter : ℝ),?_,rfl⟩
    constructor <;> nlinarith [(e.gap k).start_lt_stop,(e.star k).contact_pos,
      (e.star k).contact_lt_one]
  have hunot : u ∉ t.contacts σ := by
    obtain ⟨v,hv,hvcomp⟩ := (e.gap_isGap k).2.2
    exact connectedComponentIn_subset _ _ (hvcomp.symm ▸ hu)
  have hucl : σ u ∈ closure (d.star i).sector :=
    closure_mono ((hstar k).trans hsub) (cairns_star_contact_mem_closure_sourceStar (e.star k))
  have hunotsector : σ u ∉ (d.star i).sector := by
    obtain ⟨v,hv,hva⟩ := ha
    intro hh
    exact connectedComponentIn_subset (range σ)ᶜ v
      (hva.symm ▸ (cairns_star_sector_geometry hσ ⟨v,hv,hva⟩ (d.star i)).2.2.2 hh) (mem_range_self u)
  have huf : σ u ∈ frontier (d.star i).sector := by
    rw [(cairns_star_sector_geometry hσ ha (d.star i)).2.1.frontier_eq]
    exact ⟨hucl,hunotsector⟩
  have hcontactmono : s.contacts σ ⊆ t.contacts σ := fun u hu ↦ closure_mono hmono hu
  have huoldarc : u ∈ (d.gap i).openArc := by
    rcases (d.star i).frontier_subset huf with hb | harc
    · have hh := closure_mono (hd i) (segment_subset_closure_openSegment hb)
      exact (hunot (hcontactmono (by change σ u ∈ closure s.region; simpa only [closure_closure] using hh))).elim
    · obtain ⟨v,hv,hvu⟩ := harc
      have hvu' : v = u := hσ.injective hvu
      rw [hvu'] at hv
      rcases (d.gap i).closedArc_subset_openArc_union_endpoints hv with hh | hh
      · exact hh
      · exact (hunot (hcontactmono (hh.elim (fun hh ↦ hh.symm ▸ (d.gap_isGap i).1)
          (fun hh ↦ hh.symm ▸ (d.gap_isGap i).2.1)))).elim
  have hopen : (e.gap k).openArc ⊆ (d.gap i).openArc := by
    obtain ⟨v,hv,hvg⟩ := (e.gap_isGap k).2.2
    obtain ⟨w,hw,hwg⟩ := (d.gap_isGap i).2.2
    have hu₁ : u ∈ connectedComponentIn (t.contacts σ)ᶜ v := hvg.symm ▸ hu
    have hu₂ : u ∈ connectedComponentIn (s.contacts σ)ᶜ w := hwg.symm ▸ huoldarc
    rw [← hvg,← hwg,connectedComponentIn_eq hu₁,connectedComponentIn_eq hu₂]
    exact connectedComponentIn_mono _ (compl_subset_compl.mpr hcontactmono)
  have hclosed : IsClosed (d.gap i).closedArc :=
    (isCompact_Icc.image Circle.exp.continuous).isClosed
  have hclosure : (e.gap k).closedArc ⊆ closure (e.gap k).openArc := by
    have hh := image_closure_subset_closure_image Circle.exp.continuous
      (s := Ioo (e.gap k).start (e.gap k).stop)
    simpa only [CairnsCircleGap.closedArc, CairnsCircleGap.openArc, closure_Ioo (e.gap k).start_lt_stop.ne] using hh
  have hinc : (d.gap i).openArc ⊆ (d.gap i).closedArc := image_mono Ioo_subset_Icc_self
  exact ⟨hsub,hclosure.trans (closure_minimal (hopen.trans hinc) hclosed)⟩

end HolomorphicAnosov.Topology.Plane
