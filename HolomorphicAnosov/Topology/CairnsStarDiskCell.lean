import HolomorphicAnosov.Topology.CairnsStarTargetConvexity
import HolomorphicAnosov.Topology.CairnsClosedCellRestriction
import HolomorphicAnosov.Topology.DiskChartBoundaryAdjustment

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsStar CairnsRefinement

/-- A geometric source star is a disk cell with its actual frontier, and every
prescribed boundary homeomorphism extends over its closure. The literal radial
map identifies it with the convex target star. Restrict to closures, apply the
convex-body gauge chart, and adjust any prescribed boundary by the radial
extension of the resulting circle homeomorphism. This provides the genuine
cell hypotheses used when gluing the two initial stars. -/
theorem cairns_geometric_star_disk_cell
    {σ : Circle → ℂ} {a : Set ℂ} {g : CairnsCircleGap}
    (hσ : Topology.IsEmbedding σ) (b : StarChoice σ a g)
    (h : range σ ≃ₜ Circle) (hb : StarGeometry b h) :
    Nonempty (b.sourceStar ≃ₜ Metric.ball (0 : ℂ) 1) ∧
    Nonempty (frontier b.sourceStar ≃ₜ Metric.sphere (0 : ℂ) 1) ∧
    (∃ G : closure b.sourceStar ≃ₜ Metric.closedBall (0 : ℂ) 1,
      G '' {z : closure b.sourceStar | (z : ℂ) ∈ b.sourceStar} =
        {w : Metric.closedBall (0 : ℂ) 1 | (w : ℂ) ∈ Metric.ball (0 : ℂ) 1} ∧
      G '' {z : closure b.sourceStar | (z : ℂ) ∈ frontier b.sourceStar} =
        {w : Metric.closedBall (0 : ℂ) 1 | (w : ℂ) ∈ Metric.sphere (0 : ℂ) 1}) ∧
    (∀ e : frontier b.sourceStar ≃ₜ Metric.sphere (0 : ℂ) 1,
      ∃ G : closure b.sourceStar ≃ₜ Metric.closedBall (0 : ℂ) 1,
        ∀ z : closure b.sourceStar, ∀ hz : (z : ℂ) ∈ frontier b.sourceStar,
          (G z : ℂ) = (e ⟨z,hz⟩ : ℂ)) := by
  obtain ⟨H,hH,hinterior,hbase,hne,hopen,hball,hfront,hcoverage⟩ :=
    cairns_geometric_star_literal_extension b h hb
  obtain ⟨heq,hconvex,hγdisk,hγfront⟩ := cairns_geometric_star_target_convex hσ b h hb
  have hbounded := (Metric.isBounded_ball (x := (0 : ℂ)) (r := 1)).subset hball
  obtain ⟨G,hGint,hGfront⟩ := carrier_homeomorph_closed_disk_chart
    (range σ ∪ closure b.sourceStar)
    (range (fun z : Circle ↦ (z : ℂ)) ∪ closure (b.targetStar h))
    b.sourceStar (b.targetStar h) hb.2.1 hopen hne hconvex hbounded
    subset_union_right subset_union_right H hinterior
  have hGimage (P Q : Set ℂ)
      (hPQ : ∀ x : closure b.sourceStar, (x : ℂ) ∈ P ↔ (G x : ℂ) ∈ Q) :
      G '' {x : closure b.sourceStar | (x : ℂ) ∈ P} =
        {y : Metric.closedBall (0 : ℂ) 1 | (y : ℂ) ∈ Q} := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact (hPQ x).mp hx
    · intro hy
      refine ⟨G.symm y,(hPQ (G.symm y)).mpr ?_,G.apply_symm_apply y⟩
      simpa only [G.apply_symm_apply] using (show (y : ℂ) ∈ Q from hy)
  have hGi := hGimage _ _ hGint
  have hGf := hGimage _ _ hGfront
  refine ⟨⟨homeomorphRestrictSubsets _ _ _ _ subset_closure Metric.ball_subset_closedBall G hGint⟩,
    ⟨homeomorphRestrictSubsets _ _ _ _ frontier_subset_closure Metric.sphere_subset_closedBall G hGfront⟩,
    ⟨G,hGi,hGf⟩,?_⟩
  intro e
  obtain ⟨G',hGi',hGe⟩ := disk_chart_boundary_adjustment (closure b.sourceStar)
    (frontier b.sourceStar) b.sourceStar frontier_subset_closure G hGi hGf e
  exact ⟨G',hGe⟩

end HolomorphicAnosov.Topology.Plane
