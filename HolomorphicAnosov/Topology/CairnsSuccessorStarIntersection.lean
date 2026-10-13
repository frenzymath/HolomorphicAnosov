import HolomorphicAnosov.Topology.CairnsResidualSectorGeometry
import HolomorphicAnosov.Topology.CairnsGapRefinementCoordinates

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- The closure of an outside star meets the old stage closure exactly in its
base chord. An old closure point in the closed sector lies on its frontier,
since the open sector is disjoint from the old region. Its frontier is in
the base or the original closed gap arc. A point of that arc in the old
closure is a retained contact, hence one of the endpoints. The base belongs
to both closures by the two frontier hypotheses. Source: Cairns §4(C). -/
theorem cairns_successor_star_closure_intersection
    {σ : Circle → ℂ} {a : Set ℂ} {s : Stage}
    (hσ : Topology.IsEmbedding σ)
    (ha : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (d : StepData σ a s) (i : ResidualComponent (s.contacts σ))
    (hstar : (d.star i).sourceStar ⊆ (d.star i).sector)
    (hbase : segment ℝ (σ (d.gap i).first) (σ (d.gap i).last) ⊆
      closure (d.star i).sourceStar)
    (hold : openSegment ℝ (σ (d.gap i).first) (σ (d.gap i).last) ⊆
      closure s.region) :
    closure s.region ∩ closure (d.star i).sourceStar =
      segment ℝ (σ (d.gap i).first) (σ (d.gap i).last) := by
  have hopen := (cairns_star_sector_geometry hσ ha (d.star i)).2.1
  have hdis := (d.outside i).closure_right hopen
  have hbaseOld : segment ℝ (σ (d.gap i).first) (σ (d.gap i).last) ⊆
      closure s.region := by
    intro z hz
    have hh := closure_mono hold (segment_subset_closure_openSegment hz)
    simpa only [closure_closure] using hh
  apply Subset.antisymm
  · rintro z ⟨hzold,hzstar⟩
    have hzsector : z ∈ frontier (d.star i).sector := by
      rw [hopen.frontier_eq]
      exact ⟨closure_mono hstar hzstar, fun hz ↦ disjoint_left.mp hdis hz hzold⟩
    rcases (d.star i).frontier_subset hzsector with hzbase | hzarc
    · exact hzbase
    · obtain ⟨t,ht,rfl⟩ := hzarc
      have htS : t ∈ s.contacts σ := hzold
      rcases (d.gap i).closedArc_subset_openArc_union_endpoints ht with htopen | htend
      · obtain ⟨x,hx,hcomp⟩ := (d.gap_isGap i).2.2
        exact (connectedComponentIn_subset (s.contacts σ)ᶜ x
          (hcomp.symm ▸ htopen) htS).elim
      · rcases htend with ht | ht
        · rw [ht]
          exact left_mem_segment ℝ _ _
        · rw [ht]
          exact right_mem_segment ℝ _ _
  · intro z hz
    exact ⟨hbaseOld hz,hbase hz⟩

end HolomorphicAnosov.Topology.Plane

