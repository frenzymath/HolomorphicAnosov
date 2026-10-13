import HolomorphicAnosov.Topology.CairnsDiskCellsOpenChord
import HolomorphicAnosov.Topology.CairnsStarDiskCell
import HolomorphicAnosov.Topology.CairnsStarBaseFrontier
import HolomorphicAnosov.Topology.CairnsSuccessorOpenUnion

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- The old disk cell and each new star glue along their full base chord.
Their exact closed intersection supplies the boundary intersection; the old
proper-chord hypothesis and the star's first contact make both boundary arcs
proper. Taking the union of these local open gluings proves successor openness.
Source: Cairns §4(C), disk-cell attachments along all residual chords. -/
theorem cairns_successor_open_of_disk_cell
    {σ : Circle → ℂ} {a : Set ℂ} {s : Stage}
    (hσ : Topology.IsEmbedding σ)
    (ha : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (d : StepData σ a s) (h : range σ ≃ₜ Circle)
    (hgeo : ∀ i, StarGeometry (d.star i) h)
    (hsopen : IsOpen s.region)
    (hcell : ∃ G : closure s.region ≃ₜ Metric.closedBall (0 : ℂ) 1,
      G '' {z : closure s.region | (z : ℂ) ∈ s.region} =
        {w : Metric.closedBall (0 : ℂ) 1 | (w : ℂ) ∈ Metric.ball (0 : ℂ) 1} ∧
      G '' {z : closure s.region | (z : ℂ) ∈ frontier s.region} =
        {w : Metric.closedBall (0 : ℂ) 1 | (w : ℂ) ∈ Metric.sphere (0 : ℂ) 1})
    (hchord : ∀ i, openSegment ℝ (σ (d.gap i).first) (σ (d.gap i).last) ⊆ a)
    (hbase : ∀ i, segment ℝ (σ (d.gap i).first) (σ (d.gap i).last) ⊆ frontier s.region)
    (hproper : ∀ i, segment ℝ (σ (d.gap i).first) (σ (d.gap i).last) ≠ frontier s.region)
    (hinter : ∀ i, closure s.region ∩ closure (d.star i).sourceStar =
      segment ℝ (σ (d.gap i).first) (σ (d.gap i).last)) :
    IsOpen (d.next h).region := by
  apply cairns_successor_open_of_local_gluing d h hsopen
  intro i
  have hpq : σ (d.gap i).first ≠ σ (d.gap i).last := by
    intro he
    exact (d.gap i).start_lt_stop.ne (Circle.exp_injOn_Icc (d.gap i).shorter_than_turn
      ⟨le_rfl,(d.gap i).start_lt_stop.le⟩ ⟨(d.gap i).start_lt_stop.le,le_rfl⟩ (hσ.injective he))
  have hbaseStar : segment ℝ (σ (d.gap i).first) (σ (d.gap i).last) ⊆
      frontier (d.star i).sourceStar := fun z hz ↦ (hgeo i).2.2.2.1 ▸ Or.inl hz
  have hproperStar : segment ℝ (σ (d.gap i).first) (σ (d.gap i).last) ≠
      frontier (d.star i).sourceStar := by
    intro he
    apply cairns_star_contact_notMem_base hσ (d.star i) ha (hchord i)
    have hcf : (d.star i).contact ∈ frontier (d.star i).sourceStar :=
      (hgeo i).2.2.2.1 ▸ Or.inr (hgeo i).2.2.2.2.2.2.2.2.2.2.2.2.1.1
    exact he.symm ▸ hcf
  apply cairns_disk_cells_open_along_chord _ _ _ _ hpq _ (hbase i) hbaseStar
    (hproper i) hproperStar (hinter i)
  intro W hW
  rcases hW with rfl | rfl
  · exact hcell
  · exact (cairns_geometric_star_disk_cell hσ (d.star i) h (hgeo i)).2.2.1

end HolomorphicAnosov.Topology.Plane

