import HolomorphicAnosov.Topology.CairnsGapStrictSide

namespace HolomorphicAnosov.Topology.Plane
open Set

/-- The convex hull of a closed circle arc meets the convex hull of its
complementary closed arc precisely in the common endpoint chord. The strict
chord functional places the arcs on opposite sides; its supporting face on
the circle consists only of the endpoints. Source: Cairns §4, target caps. -/
theorem cairns_gap_closedArc_hull_inter_complement_hull (τ : Circle → ℂ)
    (hτ : Continuous τ) (hinj : Function.Injective τ) (hnorm : ∀ t, ‖τ t‖ = 1)
    (hsurj : ∀ z : ℂ, ‖z‖ = 1 → ∃ t, τ t = z) (g : CairnsCircleGap) :
    convexHull ℝ (τ '' g.closedArc) ∩ convexHull ℝ (τ '' g.openArcᶜ) =
      segment ℝ (τ g.first) (τ g.last) := by
  obtain ⟨f,hf,hends,hside,hbound⟩ :=
    cairns_gap_strict_side_functional τ hτ hinj hnorm hsurj g
  have hfirst : g.first ∈ g.closedArc := ⟨g.start,⟨le_rfl,g.start_lt_stop.le⟩,rfl⟩
  have hlast : g.last ∈ g.closedArc := ⟨g.stop,⟨g.start_lt_stop.le,le_rfl⟩,rfl⟩
  have hfirstnot : g.first ∉ g.openArc := fun hh ↦ lt_irrefl _ ((hside _).mp hh)
  have hlastnot : g.last ∉ g.openArc := fun hh ↦ hends.not_lt ((hside _).mp hh)
  have hne : τ g.first ≠ τ g.last := by
    intro he
    exact g.start_lt_stop.ne (Circle.exp_injOn_Icc g.shorter_than_turn
      ⟨le_rfl,g.start_lt_stop.le⟩ ⟨g.start_lt_stop.le,le_rfl⟩ (hinj he))
  apply opposite_circle_contact_hulls_intersection _ _ f hf _ _ (hnorm _) (hnorm _) hne hends
    (mem_image_of_mem τ hfirst) (mem_image_of_mem τ hlast)
    (mem_image_of_mem τ hfirstnot) (mem_image_of_mem τ hlastnot)
  · rintro _ ⟨t,ht,rfl⟩
    exact hnorm t
  · rintro _ ⟨t,ht,rfl⟩
    rcases g.closedArc_subset_openArc_union_endpoints ht with ht | ht
    · exact ((hside _).mp ht).le
    · rcases ht with rfl | rfl
      · exact le_rfl
      · exact hends.le
  · rintro _ ⟨t,ht,rfl⟩
    exact hbound t ht

/-- A residual closed-arc hull meets the retained contact hull exactly in its
base chord. The contact set avoids the open gap and contains both endpoints.
This is the target analogue of the outside-star intersection with the old
stage closure. Source: Cairns §4(C), affine seam compatibility. -/
theorem cairns_gap_hull_inter_contact_hull (τ : Circle → ℂ)
    (hτ : Continuous τ) (hinj : Function.Injective τ) (hnorm : ∀ t, ‖τ t‖ = 1)
    (hsurj : ∀ z : ℂ, ‖z‖ = 1 → ∃ t, τ t = z)
    (S : Set Circle) (g : CairnsCircleGap) (hg : g.IsGapOf S)
    (T : Set Circle) (hT : T ⊆ g.closedArc) (hp : g.first ∈ T) (hq : g.last ∈ T) :
    convexHull ℝ (τ '' T) ∩ convexHull ℝ (τ '' S) =
      segment ℝ (τ g.first) (τ g.last) := by
  have havoid : S ⊆ g.openArcᶜ := by
    intro t ht htg
    obtain ⟨x,hx,hcomp⟩ := hg.2.2
    exact connectedComponentIn_subset Sᶜ x (hcomp.symm ▸ htg) ht
  apply Subset.antisymm
  · intro z hz
    exact cairns_gap_closedArc_hull_inter_complement_hull τ hτ hinj hnorm hsurj g ▸
      ⟨convexHull_mono (image_mono hT) hz.1,convexHull_mono (image_mono havoid) hz.2⟩
  · intro z hz
    exact ⟨(convex_convexHull ℝ _).segment_subset
      (subset_convexHull ℝ _ (mem_image_of_mem τ hp))
      (subset_convexHull ℝ _ (mem_image_of_mem τ hq)) hz,
      (convex_convexHull ℝ _).segment_subset
      (subset_convexHull ℝ _ (mem_image_of_mem τ hg.1))
      (subset_convexHull ℝ _ (mem_image_of_mem τ hg.2.1)) hz⟩

/-- The closed arc of one residual gap misses the open arc of another.
Interior points are excluded by component disjointness; both endpoints are
retained contacts and hence lie outside every residual open arc. -/
theorem cairns_disjoint_gap_closedArc_subset_complement
    (S : Set Circle) (g v : CairnsCircleGap) (hg : g.IsGapOf S) (hv : v.IsGapOf S)
    (hdis : Disjoint g.openArc v.openArc) : v.closedArc ⊆ g.openArcᶜ := by
  intro t ht htg
  rcases v.closedArc_subset_openArc_union_endpoints ht with htv | htend
  · exact disjoint_left.mp hdis htg htv
  · have htS : t ∈ S := htend.elim (fun he ↦ he.symm ▸ hv.1) (fun he ↦ he.symm ▸ hv.2.1)
    obtain ⟨x,hx,hcomp⟩ := hg.2.2
    exact connectedComponentIn_subset Sᶜ x (hcomp.symm ▸ htg) htS

/-- Distinct residual arc hulls overlap only in the retained contact hull.
One arc hull lies in the complementary closed-arc hull of the other, so the
intersection lies on that other's endpoint chord, already in the contact hull.
Source: Cairns §4(C), separation of target patches. -/
theorem cairns_disjoint_gap_hulls_overlap_in_contact_hull (τ : Circle → ℂ)
    (hτ : Continuous τ) (hinj : Function.Injective τ) (hnorm : ∀ t, ‖τ t‖ = 1)
    (hsurj : ∀ z : ℂ, ‖z‖ = 1 → ∃ t, τ t = z)
    (S : Set Circle) (g v : CairnsCircleGap) (hg : g.IsGapOf S) (hv : v.IsGapOf S)
    (hdis : Disjoint g.openArc v.openArc) :
    convexHull ℝ (τ '' g.closedArc) ∩ convexHull ℝ (τ '' v.closedArc) ⊆
      convexHull ℝ (τ '' S) := by
  intro z hz
  have hh : z ∈ segment ℝ (τ g.first) (τ g.last) :=
    cairns_gap_closedArc_hull_inter_complement_hull τ hτ hinj hnorm hsurj g ▸
      ⟨hz.1,convexHull_mono (image_mono
        (cairns_disjoint_gap_closedArc_subset_complement S g v hg hv hdis)) hz.2⟩
  exact (convex_convexHull ℝ _).segment_subset
    (subset_convexHull ℝ _ (mem_image_of_mem τ hg.1))
    (subset_convexHull ℝ _ (mem_image_of_mem τ hg.2.1)) hh

end HolomorphicAnosov.Topology.Plane

