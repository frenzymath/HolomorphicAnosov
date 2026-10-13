import HolomorphicAnosov.Topology.CairnsStarTargetConvexity
import HolomorphicAnosov.Topology.CairnsResidualSectorGeometry

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- A target residual sector is exactly the interior of its labeled circular
arc hull, with closure equal to the full hull. The circle arc is on the hull
frontier by strict convexity, and the base chord supports the hull from the
opposite parameter gap. The bounded sector is contained in that closed convex
hull by its frontier bound. Connectedness of the convex hull interior then
identifies the two open regions. Source: Cairns §4(C), target circular caps. -/
theorem cairns_circular_arc_region_hull
    (τ : Circle → ℂ) (hτ : Topology.IsEmbedding τ)
    (hnorm : ∀ t, ‖τ t‖ = 1)
    (g : CairnsCircleGap) (V : Set ℂ) (hne : V.Nonempty) (ho : IsOpen V)
    (hball : V ⊆ Metric.ball (0 : ℂ) 1)
    (hf : frontier V ⊆ segment ℝ (τ g.first) (τ g.last) ∪ τ '' g.closedArc) :
    V = interior (convexHull ℝ (τ '' g.closedArc)) ∧
      closure V = convexHull ℝ (τ '' g.closedArc) ∧ Convex ℝ V := by
  let C := convexHull ℝ (τ '' g.closedArc)
  have hfirst : g.first ∈ g.closedArc := ⟨g.start,⟨le_rfl,g.start_lt_stop.le⟩,rfl⟩
  have hlast : g.last ∈ g.closedArc := ⟨g.stop,⟨g.start_lt_stop.le,le_rfl⟩,rfl⟩
  obtain ⟨v,hv,hvf,hvl⟩ := CairnsCircleGap.opposite_isGapOf_of_subset_closedArc
    g g.closedArc subset_rfl hfirst hlast
  have hbase : segment ℝ (τ g.first) (τ g.last) ⊆ frontier C := by
    have hh := cairns_gap_chord_subset_hull_frontier τ hτ.continuous hτ.injective
      hnorm g.closedArc v hv
    simpa only [hvf,hvl,segment_symm] using hh
  have harc : τ '' g.closedArc ⊆ frontier C := by
    apply circle_contact_subset_hull_frontier
    rintro z ⟨t,ht,rfl⟩
    exact hnorm t
  have hfront : frontier V ⊆ frontier C :=
    hf.trans (union_subset hbase harc)
  have hcompact : IsCompact C := isCompact_convexHull_finiteDimensional
    ((isCompact_Icc.image Circle.exp.continuous).image hτ.continuous)
  have hCne : C.Nonempty := ⟨τ g.first,subset_convexHull ℝ _ (mem_image_of_mem τ hfirst)⟩
  have hconvex : Convex ℝ C := convex_convexHull ℝ _
  have hbounded : Bornology.IsBounded V := Metric.isBounded_ball.subset hball
  have hsub : V ⊆ C := bounded_subset_closed_convex_of_frontier _ C hbounded
    hconvex hcompact.isClosed hCne
    (hfront.trans (frontier_subset_iff_isClosed.mpr hcompact.isClosed))
  have heq := open_eq_convex_interior_of_frontier_subset _ C ho hne hsub hconvex hfront
  refine ⟨heq,?_,heq.symm ▸ hconvex.interior⟩
  rw [heq,hconvex.closure_interior_eq_closure_of_nonempty_interior (heq ▸ hne),
    hcompact.isClosed.closure_eq]

/-- Specialize the circular-arc hull characterization to a chosen target
chord sector. Its raw component data supplies openness, nonemptiness and the
frontier bound. Source: Cairns §4(C), target circular caps. -/
theorem cairns_target_sector_hull
    (τ : Circle → ℂ) (hτ : Topology.IsEmbedding τ)
    (hnorm : ∀ t, ‖τ t‖ = 1)
    (hcomponent : ∃ x ∈ Metric.ball (0 : ℂ) 1,
      connectedComponentIn (range τ)ᶜ x = Metric.ball (0 : ℂ) 1)
    (g : CairnsCircleGap) (b : StarChoice τ (Metric.ball (0 : ℂ) 1) g) :
    b.sector = interior (convexHull ℝ (τ '' g.closedArc)) ∧
      closure b.sector = convexHull ℝ (τ '' g.closedArc) ∧ Convex ℝ b.sector := by
  obtain ⟨hne,ho,hconn,hball⟩ := cairns_star_sector_geometry hτ hcomponent b
  exact cairns_circular_arc_region_hull τ hτ hnorm g b.sector hne ho hball b.frontier_subset

end HolomorphicAnosov.Topology.Plane

