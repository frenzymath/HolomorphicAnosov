import HolomorphicAnosov.Topology.CairnsGapSupportingChord
import HolomorphicAnosov.Topology.CairnsGapRefinementCoordinates

namespace HolomorphicAnosov.Topology.Plane
open Set

/-- For a homeomorphic parametrization of the unit circle, a proper parameter
arc is exactly one strict side of its endpoint chord. The supporting functional
of the complementary closed arc has no zero on the given open arc, hence a
constant strict sign there. If that sign were negative, the whole circle would
lie on one side of a line through two distinct circle points, contradicting
strict convexity of the disk. This also treats orientation reversal. -/
theorem cairns_gap_strict_side_functional (σ : Circle → ℂ)
    (hσ : Continuous σ) (hinj : Function.Injective σ) (hnorm : ∀ t, ‖σ t‖ = 1)
    (hsurj : ∀ z : ℂ, ‖z‖ = 1 → ∃ t, σ t = z) (g : CairnsCircleGap) :
    ∃ f : ℂ →L[ℝ] ℝ, f ≠ 0 ∧ f (σ g.first) = f (σ g.last) ∧
      (∀ t, t ∈ g.openArc ↔ f (σ g.first) < f (σ t)) ∧
      (∀ t, t ∉ g.openArc → f (σ t) ≤ f (σ g.first)) := by
  have hfnot : g.first ∉ g.openArc := by
    rintro ⟨θ,hθ,he⟩
    exact hθ.1.ne' (Circle.exp_injOn_Icc g.shorter_than_turn
      ⟨hθ.1.le,hθ.2.le⟩ ⟨le_rfl,g.start_lt_stop.le⟩ he)
  have hlnot : g.last ∉ g.openArc := by
    rintro ⟨θ,hθ,he⟩
    exact hθ.2.ne (Circle.exp_injOn_Icc g.shorter_than_turn
      ⟨hθ.1.le,hθ.2.le⟩ ⟨g.start_lt_stop.le,le_rfl⟩ he)
  have hg : g.IsGapOf g.openArcᶜ :=
    CairnsCircleGap.isGapOf_of_endpoints g _ hfnot hlnot (fun t ht hn ↦ hn ht)
  obtain ⟨f,hf,hends,hbound⟩ := cairns_gap_supporting_functional σ hσ hinj hnorm _ g hg
  have hne : σ g.first ≠ σ g.last := by
    intro he
    have hh := Circle.exp_injOn_Icc g.shorter_than_turn
      ⟨le_rfl,g.start_lt_stop.le⟩ ⟨g.start_lt_stop.le,le_rfl⟩ (hinj he)
    exact g.start_lt_stop.ne hh
  let F : Circle → ℝ := fun t ↦ f (σ t) - f (σ g.first)
  have hFc : Continuous F := (f.continuous.comp hσ).sub continuous_const
  have hnz : ∀ t ∈ g.openArc, F t ≠ 0 := by
    intro t ht hz
    have he := circle_functional_level_two_points f hf _ _ _ (hnorm _) (hnorm _) (hnorm _)
      hne hends (sub_eq_zero.mp hz)
    rcases he with he | he
    · exact hfnot (hinj he ▸ ht)
    · exact hlnot (hinj he ▸ ht)
  have hpre : IsPreconnected (F '' g.openArc) :=
    (isPreconnected_Ioo.image Circle.exp Circle.exp.continuous.continuousOn).image F hFc.continuousOn
  have hcover : F '' g.openArc ⊆ Iio 0 ∪ Ioi 0 := by
    rintro _ ⟨t,ht,rfl⟩
    exact lt_or_gt_of_ne (hnz t ht)
  have hdisj : (F '' g.openArc) ∩ (Iio 0 ∩ Ioi 0) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro t ht
    exact lt_asymm (show t < 0 from ht.2.1) (show 0 < t from ht.2.2)
  have hpositive : ∀ t ∈ g.openArc, f (σ g.first) < f (σ t) := by
    rcases isPreconnected_iff_subset_of_disjoint.mp hpre _ _ isOpen_Iio isOpen_Ioi
      hcover hdisj with hneg | hpos
    · obtain ⟨z,hz,hfz⟩ := circle_functional_equal_pair_not_upper_bound f hf
        (σ g.first) (σ g.last) (hnorm _) (hnorm _) hne hends
      obtain ⟨t,rfl⟩ := hsurj z hz
      have hle : f (σ t) ≤ f (σ g.first) := by
        by_cases ht : t ∈ g.openArc
        · exact (sub_neg.mp (show F t < 0 from hneg (mem_image_of_mem F ht))).le
        · exact hbound t ht
      exact (hfz.not_ge hle).elim
    · intro t ht
      exact sub_pos.mp (show 0 < F t from hpos (mem_image_of_mem F ht))
  refine ⟨f,hf,hends,?_,hbound⟩
  intro t
  constructor
  · exact hpositive t
  · intro ht
    by_contra hnot
    exact ht.not_ge (hbound t hnot)

/-- Contact hulls from complementary parameter arcs have exactly their common
base chord in common, independently of the orientation of the circle map.
The strict-side functional of the first arc places its contacts above the
base and the opposite contacts below it; use the supporting-face intersection
calculation for circle-contact hulls. -/
theorem cairns_opposite_arc_contact_hulls_intersection (σ : Circle → ℂ)
    (hσ : Continuous σ) (hinj : Function.Injective σ) (hnorm : ∀ t, ‖σ t‖ = 1)
    (hsurj : ∀ z : ℂ, ‖z‖ = 1 → ∃ t, σ t = z)
    (g₁ g₂ : CairnsCircleGap)
    (hstart : g₂.start = g₁.stop) (hstop : g₂.stop = g₁.start + 2 * Real.pi)
    (hf : g₂.first = g₁.last) (hl : g₂.last = g₁.first)
    (S T : Set Circle) (hS : S ⊆ g₁.closedArc) (hT : T ⊆ g₂.closedArc)
    (hpS : g₁.first ∈ S) (hqS : g₁.last ∈ S)
    (hpT : g₁.first ∈ T) (hqT : g₁.last ∈ T) :
    convexHull ℝ (σ '' S) ∩ convexHull ℝ (σ '' T) =
      segment ℝ (σ g₁.first) (σ g₁.last) := by
  obtain ⟨f,hfnz,hends,hside,hbound⟩ := cairns_gap_strict_side_functional σ hσ hinj hnorm hsurj g₁
  have hne : σ g₁.first ≠ σ g₁.last := by
    intro he
    exact g₁.start_lt_stop.ne (Circle.exp_injOn_Icc g₁.shorter_than_turn
      ⟨le_rfl,g₁.start_lt_stop.le⟩ ⟨g₁.start_lt_stop.le,le_rfl⟩ (hinj he))
  have hSpos : ∀ t ∈ S, f (σ g₁.first) ≤ f (σ t) := by
    intro t ht
    rcases CairnsCircleGap.closedArc_subset_openArc_union_endpoints g₁ (hS ht) with ht | ht
    · exact ((hside t).mp ht).le
    · rcases ht with rfl | rfl
      · exact le_rfl
      · exact hends.le
  have hTneg : ∀ t ∈ T, f (σ t) ≤ f (σ g₁.first) := by
    intro t ht
    apply hbound t
    intro htarc
    have ht₁ : t ∈ g₁.closedArc := by
      obtain ⟨θ,hθ,rfl⟩ := htarc
      exact ⟨θ,⟨hθ.1.le,hθ.2.le⟩,rfl⟩
    have hm := (CairnsCircleGap.opposite_parameter_cover_inter g₁ g₂ hstart hstop hf hl).2
    rw [(CairnsCircleGap.parameter_embedding_range g₁).2.1,
      (CairnsCircleGap.parameter_embedding_range g₂).2.1] at hm
    have hend : t ∈ ({g₁.first,g₁.last} : Set Circle) := hm ▸ (show
      t ∈ g₁.closedArc ∩ g₂.closedArc from ⟨ht₁,hT ht⟩)
    have hlt := (hside t).mp htarc
    rcases hend with rfl | rfl
    · exact lt_irrefl _ hlt
    · exact hends.not_lt hlt
  apply opposite_circle_contact_hulls_intersection _ _ f hfnz _ _ (hnorm _) (hnorm _) hne hends
    (mem_image_of_mem σ hpS) (mem_image_of_mem σ hqS)
    (mem_image_of_mem σ hpT) (mem_image_of_mem σ hqT)
  · rintro _ ⟨t,ht,rfl⟩;exact hnorm t
  · rintro _ ⟨t,ht,rfl⟩;exact hSpos t ht
  · rintro _ ⟨t,ht,rfl⟩;exact hTneg t ht

end HolomorphicAnosov.Topology.Plane
