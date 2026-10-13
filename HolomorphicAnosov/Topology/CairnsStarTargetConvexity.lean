import HolomorphicAnosov.Topology.CairnsGeometricStarChoice
import HolomorphicAnosov.Topology.CairnsGapSupportingChord
import HolomorphicAnosov.Topology.CairnsGapRefinementCoordinates

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsStar CairnsRefinement

/-- A contact-free parameter interval in a star front is a genuine gap of
its global circle contact set. Injectivity identifies its recorded endpoint
coordinates; the interval itself is the corresponding angular subgap. -/
theorem cairns_front_pair_is_circle_gap {σ : Circle → ℂ}
    (hinj : Function.Injective σ) (g : CairnsCircleGap) (C : Set ℂ)
    (u v : I) (hp : (σ (g.parameter u),σ (g.parameter v)) ∈
      gapPairs (fun t ↦ σ (g.parameter t)) C) :
    ∃ gg : CairnsCircleGap, gg.IsGapOf (σ ⁻¹' C) ∧
      gg.first = g.parameter u ∧ gg.last = g.parameter v := by
  obtain ⟨l,r,hlr,hl,hr,hmissing,he⟩ := hp
  have hu : u = l := (CairnsCircleGap.parameter_embedding_range g).1.injective
    (hinj (congrArg Prod.fst he))
  have hv : v = r := (CairnsCircleGap.parameter_embedding_range g).1.injective
    (hinj (congrArg Prod.snd he))
  subst u; subst v
  refine ⟨g.subgap l r hlr,?_,rfl,rfl⟩
  apply CairnsCircleGap.isGapOf_of_endpoints _ _ hl hr
  rw [CairnsCircleGap.subgap_openArc]
  rintro _ ⟨t,⟨hlt,htr⟩,rfl⟩
  exact hmissing t hlt htr

/-- The target front of a geometric star lies on the frontier of its retained
circle-contact hull. Original contacts are circle points. Every other point
is an affine front-chord value, whose parameter interval is an actual gap and
therefore a supporting chord of that hull. -/
theorem cairns_star_target_front_subset_hull_frontier
    {σ : Circle → ℂ} {a : Set ℂ} {g : CairnsCircleGap}
    (hσ : Topology.IsEmbedding σ) (b : StarChoice σ a g)
    (h : range σ ≃ₜ Circle)
    (hcoverage : ∀ z ∈ b.front, z ∉ range σ → ∃ w, b.FrontCoordinate z w) :
    let τ := fun t : Circle ↦ (h ⟨σ t,⟨t,rfl⟩⟩ : ℂ)
    b.targetFront h ⊆ frontier (convexHull ℝ (τ '' (σ ⁻¹' (b.front ∩ range σ)))) := by
  classical
  intro τ
  have hτ : Continuous τ := continuous_subtype_val.comp
    (h.continuous.comp (hσ.continuous.subtype_mk (fun t ↦ ⟨t,rfl⟩)))
  have hτinj : Function.Injective τ := by
    intro s t he
    exact hσ.injective (congrArg Subtype.val (h.injective (Subtype.ext he)))
  have hτnorm : ∀ t, ‖τ t‖ = 1 := fun t ↦ Circle.norm_coe _
  rintro z ⟨w,hw,rfl⟩
  unfold StarChoice.frontMap
  split_ifs with hc hcoord
  · have hn : ∀ v ∈ τ '' (σ ⁻¹' (b.front ∩ range σ)), ‖v‖ = 1 := by
      rintro _ ⟨t,ht,rfl⟩
      exact hτnorm t
    apply circle_contact_subset_hull_frontier _ hn
    obtain ⟨t,rfl⟩ := hc
    exact ⟨t,⟨hw,⟨t,rfl⟩⟩,rfl⟩
  · have hchosen := Classical.choose_spec hcoord
    obtain ⟨gg,hgg,hfirst,hlast⟩ := cairns_front_pair_is_circle_gap hσ.injective g
      (b.front ∩ range σ) _ _ hchosen.1
    apply cairns_gap_chord_subset_hull_frontier τ hτ hτinj hτnorm _ gg hgg
    rw [hfirst,hlast]
    exact ⟨1-(Classical.choose hcoord).2.2,(Classical.choose hcoord).2.2,
      sub_nonneg.mpr (Classical.choose hcoord).2.2.property.2,
      (Classical.choose hcoord).2.2.property.1,sub_add_cancel _ _,rfl⟩
  · exact (hcoord (hcoverage w hw hc)).elim

/-- Each literal geometric target star is exactly the interior of the convex
hull of its retained target contacts. The outer front consists of supporting
contact chords; the base is the chord of the opposite, contact-free arc.
The bounded-region hull lemma and connected convex interior identify the star.
This proves its disk type from the single-star construction itself. -/
theorem cairns_geometric_star_target_convex
    {σ : Circle → ℂ} {a : Set ℂ} {g : CairnsCircleGap}
    (hσ : Topology.IsEmbedding σ) (b : StarChoice σ a g)
    (h : range σ ≃ₜ Circle) (hb : StarGeometry b h) :
    let τ := fun t : Circle ↦ (h ⟨σ t,⟨t,rfl⟩⟩ : ℂ)
    b.targetStar h = interior (convexHull ℝ (τ '' (σ ⁻¹' (b.front ∩ range σ)))) ∧
      Convex ℝ (b.targetStar h) ∧
      Nonempty (b.targetStar h ≃ₜ Metric.ball (0 : ℂ) 1) ∧
      Nonempty (frontier (b.targetStar h) ≃ₜ Metric.sphere (0 : ℂ) 1) := by
  intro τ
  obtain ⟨H,hH,hint,hbase,hne,hopen,hball,hfront,hcoverage⟩ :=
    cairns_geometric_star_literal_extension b h hb
  rcases hb with ⟨hBne,hBopen,hBsub,hBfront,hLc,hBsweep,hBstar,hBunique,
    hCclosed,hCsub,hD₁,hD₂,hPC,hCurveCl,hrest⟩
  let S := σ ⁻¹' (b.front ∩ range σ)
  let C := convexHull ℝ (τ '' S)
  have hτ : Continuous τ := continuous_subtype_val.comp
    (h.continuous.comp (hσ.continuous.subtype_mk (fun t ↦ ⟨t,rfl⟩)))
  have hτinj : Function.Injective τ := by
    intro s t he
    exact hσ.injective (congrArg Subtype.val (h.injective (Subtype.ext he)))
  have hτnorm : ∀ t, ‖τ t‖ = 1 := fun t ↦ Circle.norm_coe _
  have hSclosed : IsClosed S := hCclosed.preimage hσ.continuous
  have hSsub : S ⊆ g.closedArc := by
    intro t ht
    obtain ⟨u,hu,he⟩ := hCsub ht
    have hut : u = t := hσ.injective he
    rw [← hut,← (CairnsCircleGap.parameter_embedding_range g).2.1]
    exact hu
  obtain ⟨gg,hgg,hgf,hgl⟩ :=
    CairnsCircleGap.opposite_isGapOf_of_subset_closedArc g S hSsub hD₁ hD₂
  have hbaseHull : segment ℝ (τ g.first) (τ g.last) ⊆ frontier C := by
    have hh := cairns_gap_chord_subset_hull_frontier τ hτ hτinj hτnorm S gg hgg
    simpa only [hgf,hgl,segment_symm] using hh
  have hfrontHull : frontier (b.targetStar h) ⊆ frontier C := by
    rw [hfront]
    exact union_subset hbaseHull (cairns_star_target_front_subset_hull_frontier hσ b h hcoverage)
  have hcompact : IsCompact C :=
    isCompact_convexHull_finiteDimensional (hSclosed.isCompact.image hτ)
  have hCne : C.Nonempty :=
    ⟨τ g.first,subset_convexHull ℝ _ (mem_image_of_mem τ hD₁)⟩
  have hCconvex : Convex ℝ C := convex_convexHull ℝ _
  have hbounded : Bornology.IsBounded (b.targetStar h) :=
    (Metric.isBounded_ball (x := (0 : ℂ)) (r := 1)).subset hball
  have hsub : b.targetStar h ⊆ C :=
    bounded_subset_closed_convex_of_frontier _ C hbounded hCconvex hcompact.isClosed hCne
      (hfrontHull.trans (frontier_subset_iff_isClosed.mpr hcompact.isClosed))
  have heq := open_eq_convex_interior_of_frontier_subset _ C hopen hne hsub hCconvex hfrontHull
  refine ⟨heq,?_,open_convex_body_disk_charts _ C hopen hne hsub hCconvex
    hcompact.isBounded hcompact.isClosed hfrontHull⟩
  rw [heq]
  exact hCconvex.interior

/-- The closure of a geometric target star is its compact contact hull.
The hull has nonempty interior, equal to the target star; a convex set with
nonempty interior has the same closure as its interior. -/
theorem cairns_geometric_star_target_closure
    {σ : Circle → ℂ} {a : Set ℂ} {g : CairnsCircleGap}
    (hσ : Topology.IsEmbedding σ) (b : StarChoice σ a g)
    (h : range σ ≃ₜ Circle) (hb : StarGeometry b h) :
    let τ := fun t : Circle ↦ (h ⟨σ t,⟨t,rfl⟩⟩ : ℂ)
    closure (b.targetStar h) = convexHull ℝ (τ '' (σ ⁻¹' (b.front ∩ range σ))) := by
  intro τ
  have heq := (cairns_geometric_star_target_convex hσ b h hb).1
  have hτ : Continuous τ := continuous_subtype_val.comp
    (h.continuous.comp (hσ.continuous.subtype_mk (fun t ↦ ⟨t,rfl⟩)))
  have hCclosed : IsClosed (b.front ∩ range σ) := hb.2.2.2.2.2.2.2.2.1
  have hcompact := isCompact_convexHull_finiteDimensional
    ((hCclosed.preimage hσ.continuous).isCompact.image hτ)
  obtain ⟨H,hH,hi,hbase,hne,hrest⟩ := cairns_geometric_star_literal_extension b h hb
  have hint : (interior (convexHull ℝ (τ '' (σ ⁻¹' (b.front ∩ range σ))))).Nonempty := heq ▸ hne
  rw [heq,(convex_convexHull ℝ _).closure_interior_eq_closure_of_nonempty_interior hint,
    hcompact.isClosed.closure_eq]

end HolomorphicAnosov.Topology.Plane
