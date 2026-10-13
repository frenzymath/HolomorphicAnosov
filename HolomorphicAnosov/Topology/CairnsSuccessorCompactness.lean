import HolomorphicAnosov.Topology.CairnsNullPatchPasting
import HolomorphicAnosov.Topology.CairnsGapNullFamily
import HolomorphicAnosov.Topology.CairnsResidualSectorGeometry

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement
open scoped _root_.Topology

/-- Distinct literal residual labels have disjoint open arcs, since the labels
are actual connected components. A common point would identify both connected
components and then both subtype labels. Source: Cairns §4(C), gap indexing. -/
theorem cairns_step_gap_pairwise_disjoint
    {σ : Circle → ℂ} {a : Set ℂ} {s : Stage} (d : StepData σ a s) :
    Pairwise fun i j ↦ Disjoint (d.gap i).openArc (d.gap j).openArc := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hxi hxj
  obtain ⟨u,hu,hui⟩ := i.property
  obtain ⟨v,hv,hvj⟩ := j.property
  have hxui : x ∈ connectedComponentIn (s.contacts σ)ᶜ u :=
    hui.symm ▸ (d.gap_arc i ▸ hxi)
  have hxvj : x ∈ connectedComponentIn (s.contacts σ)ᶜ v :=
    hvj.symm ▸ (d.gap_arc j ▸ hxj)
  apply hij
  apply Subtype.ext
  exact hui.symm.trans ((connectedComponentIn_eq hxui).trans
    ((connectedComponentIn_eq hxvj).symm.trans hvj))

/-- The old stage closure together with all new closed stars is compact.
The first endpoint of each gap belongs to the old closure. The sector bound
puts its whole star in the closed disk about that endpoint whose radius is the
diameter of its original boundary arc. Distinct residual arcs have diameters
tending to zero. The compact null-patch union theorem therefore controls every
accumulation point. Source: Cairns §4(C), pp.864–865. -/
theorem cairns_successor_closed_stars_compact
    {σ : Circle → ℂ} {a : Set ℂ} {s : Stage}
    (hσ : Topology.IsEmbedding σ)
    (ha : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (haBounded : Bornology.IsBounded a) (d : StepData σ a s)
    (hs : Bornology.IsBounded s.region)
    (hstar : ∀ i, (d.star i).sourceStar ⊆ (d.star i).sector) :
    IsCompact (closure s.region ∪ ⋃ i, closure (d.star i).sourceStar) := by
  let size := fun i ↦ Metric.diam (σ '' (d.gap i).closedArc)
  have hbounded (i) : Bornology.IsBounded (d.star i).sourceStar :=
    haBounded.subset ((hstar i).trans (cairns_star_sector_geometry hσ ha (d.star i)).2.2.2)
  apply null_patch_union_isCompact (closure s.region) hs.isCompact_closure
    (fun i ↦ closure (d.star i).sourceStar) (fun i ↦ (hbounded i).isCompact_closure)
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
      (d.star i) _ _ harc (closure_mono (hstar i) hz)
  · intro j hj
    exact CairnsCircleGap.image_diam_tendsto_zero_of_disjoint σ hσ.continuous d.gap
      (cairns_step_gap_pairwise_disjoint d) j hj

end HolomorphicAnosov.Topology.Plane

