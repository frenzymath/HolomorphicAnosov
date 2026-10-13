import HolomorphicAnosov.Topology.CairnsSuccessorCompactness
import HolomorphicAnosov.Topology.CairnsGapRefinementCoordinates
import HolomorphicAnosov.Topology.CairnsResidualStageContacts

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- Selected outside sectors for distinct residual gaps are disjoint. They
are components of the old residual region, so an intersection makes them
equal. The first contact of one star would then lie on the other's frontier.
It lies in the interior of its own gap and hence outside the old contacts;
the other frontier's base belongs to the old closure and its original arc
has disjoint interior. Both possible frontier locations are impossible.
Source: Cairns §4(C), disjoint outside-sector family. -/
theorem cairns_successor_sectors_pairwise_disjoint
    {σ : Circle → ℂ} {a : Set ℂ} {s : Stage}
    (hσ : Topology.IsEmbedding σ)
    (ha : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (d : StepData σ a s)
    (hstar : ∀ i, (d.star i).sourceStar ⊆ (d.star i).sector)
    (hchord : ∀ i, openSegment ℝ (σ (d.gap i).first) (σ (d.gap i).last) ⊆
      closure s.region) :
    Pairwise fun i j ↦ Disjoint (d.star i).sector (d.star j).sector := by
  intro i j hij
  apply disjoint_left.mpr
  intro z hzi hzj
  obtain ⟨x,hx,hxi⟩ := cairns_star_sector_component_outside_closure
    hσ ha (d.star i) s.region (d.outside i) (hchord i)
  obtain ⟨y,hy,hyj⟩ := cairns_star_sector_component_outside_closure
    hσ ha (d.star j) s.region (d.outside j) (hchord j)
  have hsectors : (d.star i).sector = (d.star j).sector :=
    hxi.symm.trans ((connectedComponentIn_eq (hxi.symm ▸ hzi)).trans
      ((connectedComponentIn_eq (hyj.symm ▸ hzj)).symm.trans hyj))
  let t := (d.gap i).parameter (d.star i).contactParameter
  have htopen : t ∈ (d.gap i).openArc := by
    refine ⟨(d.gap i).start + ((d.gap i).stop - (d.gap i).start) *
      ((d.star i).contactParameter : ℝ),?_,rfl⟩
    constructor <;> nlinarith [(d.gap i).start_lt_stop,
      (d.star i).contact_pos,(d.star i).contact_lt_one]
  have htS : t ∉ s.contacts σ := by
    obtain ⟨u,hu,hug⟩ := (d.gap_isGap i).2.2
    exact connectedComponentIn_subset _ _ (hug.symm ▸ htopen)
  have htcl : σ t ∈ closure (d.star j).sector := by
    rw [← hsectors]
    exact closure_mono (hstar i) (cairns_star_contact_mem_closure_sourceStar (d.star i))
  have hcurve : σ t ∉ a := by
    obtain ⟨u,hu,hua⟩ := ha
    intro ht
    exact connectedComponentIn_subset (range σ)ᶜ u (hua.symm ▸ ht) (mem_range_self t)
  have htfront : σ t ∈ frontier (d.star j).sector := by
    rw [(cairns_star_sector_geometry hσ ha (d.star j)).2.1.frontier_eq]
    exact ⟨htcl,fun ht ↦ hcurve ((cairns_star_sector_geometry hσ ha (d.star j)).2.2.2 ht)⟩
  rcases (d.star j).frontier_subset htfront with htbase | htarc
  · have hh := closure_mono (hchord j) (segment_subset_closure_openSegment htbase)
    apply htS
    change σ t ∈ closure s.region
    simpa only [closure_closure] using hh
  · obtain ⟨u,hu,he⟩ := htarc
    have htu : u = t := hσ.injective he
    subst u
    rcases (d.gap j).closedArc_subset_openArc_union_endpoints hu with htj | htj
    · exact disjoint_left.mp (cairns_step_gap_pairwise_disjoint d hij) htopen htj
    · rcases htj with htj | htj
      · exact htS (htj.symm ▸ (d.gap_isGap j).1)
      · exact htS (htj.symm ▸ (d.gap_isGap j).2.1)

/-- Two distinct new closed stars can overlap only in the old carrier.
The sectors are disjoint and open, so a common closure point is on the first
sector frontier. That frontier consists of its old chord and original arc;
the chord lies in the old closure and the arc is on the original curve.
Source: Cairns §4(C), compatibility of radial patch extensions. -/
theorem cairns_successor_star_overlap_in_old_carrier
    {σ : Circle → ℂ} {a : Set ℂ} {s : Stage}
    (hσ : Topology.IsEmbedding σ)
    (ha : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (d : StepData σ a s)
    (hstar : ∀ i, (d.star i).sourceStar ⊆ (d.star i).sector)
    (hchord : ∀ i, openSegment ℝ (σ (d.gap i).first) (σ (d.gap i).last) ⊆
      closure s.region) :
    ∀ i j, i ≠ j → closure (d.star i).sourceStar ∩ closure (d.star j).sourceStar ⊆
      closure s.region ∪ range σ := by
  intro i j hij z hz
  have hraw := cairns_successor_sectors_pairwise_disjoint hσ ha d hstar hchord hij
  have hdis := Disjoint.closure_right hraw (cairns_star_sector_geometry hσ ha (d.star i)).2.1
  have hzfront : z ∈ frontier (d.star i).sector := by
    rw [(cairns_star_sector_geometry hσ ha (d.star i)).2.1.frontier_eq]
    exact ⟨closure_mono (hstar i) hz.1,
      fun hi ↦ disjoint_left.mp hdis hi (closure_mono (hstar j) hz.2)⟩
  rcases (d.star i).frontier_subset hzfront with hb | hc
  · left
    have hh := closure_mono (hchord i) (segment_subset_closure_openSegment hb)
    simpa only [closure_closure] using hh
  · exact Or.inr (image_subset_range _ _ hc)

end HolomorphicAnosov.Topology.Plane

