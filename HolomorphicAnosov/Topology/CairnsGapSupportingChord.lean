import HolomorphicAnosov.Topology.CairnsCircleContactHull
import HolomorphicAnosov.Topology.CairnsGapParameter

namespace HolomorphicAnosov.Topology.Plane
open Set
open scoped ComplexConjugate

/-- Each complementary arc determines a supporting line of the convex hull of
retained unit-circle contacts. The opposite open arc is connected, so its
chord determinant has one strict sign. All retained points lie in its closure;
choose the sign of the nonzero chord functional accordingly. -/
theorem cairns_gap_supporting_functional (σ : Circle → ℂ)
    (hσ : Continuous σ) (hinj : Function.Injective σ) (hnorm : ∀ t, ‖σ t‖ = 1)
    (S : Set Circle) (g : CairnsCircleGap) (hg : g.IsGapOf S) :
    ∃ f : ℂ →L[ℝ] ℝ, f ≠ 0 ∧ f (σ g.first) = f (σ g.last) ∧
      ∀ t ∈ S, f (σ t) ≤ f (σ g.first) := by
  let g' : CairnsCircleGap := {
    start := g.stop
    stop := g.start + 2 * Real.pi
    start_lt_stop := by linarith [g.shorter_than_turn]
    shorter_than_turn := by linarith [g.start_lt_stop] }
  have hfirst : g'.first = g.last := rfl
  have hlast : g'.last = g.first := Circle.periodic_exp g.start
  have hne : g.first ≠ g.last := by
    intro he
    exact g.start_lt_stop.ne (Circle.exp_injOn_Icc g.shorter_than_turn
      ⟨le_rfl,g.start_lt_stop.le⟩ ⟨g.start_lt_stop.le,le_rfl⟩ he)
  have hne' : σ g.first ≠ σ g.last := fun he ↦ hne (hinj he)
  let d := σ g.last - σ g.first
  let f : ℂ →L[ℝ] ℝ := d.re • Complex.imCLM - d.im • Complex.reCLM
  have hf_apply (z : ℂ) : f z = d.re * z.im - d.im * z.re := rfl
  have hfnz : f ≠ 0 := by
    intro hf
    have hre := congrArg (fun F : ℂ →L[ℝ] ℝ ↦ F Complex.I) hf
    have him := congrArg (fun F : ℂ →L[ℝ] ℝ ↦ F 1) hf
    change d.re * Complex.I.im - d.im * Complex.I.re = 0 at hre
    change d.re * (1 : ℂ).im - d.im * (1 : ℂ).re = 0 at him
    simp only [Complex.I_im,Complex.I_re,mul_one,mul_zero,sub_zero] at hre
    simp only [Complex.one_im,Complex.one_re,mul_one,mul_zero,zero_sub,neg_eq_zero] at him
    apply hne'
    apply Complex.ext <;> dsimp [d] at hre him
    · linarith
    · linarith
  have hends : f (σ g.first) = f (σ g.last) := by
    simp only [hf_apply]
    dsimp [d]
    ring
  let F : Circle → ℝ := fun t ↦ f (σ t) - f (σ g.first)
  have hFc : Continuous F := (f.continuous.comp hσ).sub continuous_const
  have hzero (t : Circle) (ht : F t = 0) : t = g.first ∨ t = g.last := by
    have he : f (σ t) = f (σ g.first) := sub_eq_zero.mp ht
    exact (circle_functional_level_two_points f hfnz _ _ _ (hnorm _) (hnorm _)
      (hnorm _) hne' hends he).imp (fun hh ↦ hinj hh) (fun hh ↦ hinj hh)
  have havoid : g.openArc ⊆ Sᶜ := by
    obtain ⟨_,_,x,hx,heq⟩ := hg
    rw [← heq]
    exact connectedComponentIn_subset _ _
  have hopzero : ∀ t ∈ g'.openArc, F t ≠ 0 := by
    intro t ht hz
    obtain ⟨θ,hθ,hθt⟩ := ht
    rcases hzero t hz with he | he
    · have hh : Circle.exp θ = Circle.exp g'.stop := by
        exact hθt.trans (he.trans hlast.symm)
      have hh' := Circle.exp_injOn_Icc g'.shorter_than_turn
        ⟨hθ.1.le,hθ.2.le⟩ ⟨g'.start_lt_stop.le,le_rfl⟩ hh
      exact hθ.2.ne hh'
    · have hh : Circle.exp θ = Circle.exp g'.start := by
        exact hθt.trans (he.trans hfirst.symm)
      have hh' := Circle.exp_injOn_Icc g'.shorter_than_turn
        ⟨hθ.1.le,hθ.2.le⟩ ⟨le_rfl,g'.start_lt_stop.le⟩ hh
      exact hθ.1.ne' hh'
  have hclosedSub : g'.closedArc ⊆ closure g'.openArc := by
    have hh := image_closure_subset_closure_image Circle.exp.continuous
      (s := Ioo g'.start g'.stop)
    change Circle.exp '' Icc g'.start g'.stop ⊆
      closure (Circle.exp '' Ioo g'.start g'.stop)
    simpa only [closure_Ioo g'.start_lt_stop.ne] using hh
  have hretained : S ⊆ closure g'.openArc := by
    intro t ht
    obtain ⟨hcover,-⟩ := CairnsCircleGap.opposite_parameter_cover_inter g g' rfl rfl hfirst hlast
    have hcov : t ∈ range g.parameter ∪ range g'.parameter := hcover.symm ▸ mem_univ t
    apply hclosedSub
    rcases hcov with htG | htG
    · rw [(CairnsCircleGap.parameter_embedding_range g).2.1] at htG
      obtain ⟨θ,hθ,rfl⟩ := htG
      have hend : θ = g.start ∨ θ = g.stop := by
        by_contra hn
        push Not at hn
        exact havoid ⟨θ,⟨lt_of_le_of_ne hθ.1 hn.1.symm,
          lt_of_le_of_ne hθ.2 hn.2⟩,rfl⟩ ht
      rcases hend with rfl | rfl
      · exact ⟨g'.stop,⟨g'.start_lt_stop.le,le_rfl⟩,hlast⟩
      · exact ⟨g'.start,⟨le_rfl,g'.start_lt_stop.le⟩,rfl⟩
    · exact (CairnsCircleGap.parameter_embedding_range g').2.1 ▸ htG
  have hpre : IsPreconnected (F '' g'.openArc) :=
    (isPreconnected_Ioo.image Circle.exp Circle.exp.continuous.continuousOn).image F hFc.continuousOn
  have hcover : F '' g'.openArc ⊆ Iio 0 ∪ Ioi 0 := by
    rintro _ ⟨t,ht,rfl⟩
    exact lt_or_gt_of_ne (hopzero t ht)
  have hdisj : (F '' g'.openArc) ∩ (Iio 0 ∩ Ioi 0) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro t ht
    exact lt_asymm (show t < 0 from ht.2.1) (show 0 < t from ht.2.2)
  rcases isPreconnected_iff_subset_of_disjoint.mp hpre _ _ isOpen_Iio isOpen_Ioi
    hcover hdisj with hneg | hpos
  · have hcl : closure g'.openArc ⊆ {t | F t ≤ 0} :=
      closure_minimal (fun t ht ↦ (show F t < 0 from hneg (mem_image_of_mem F ht)).le)
        (isClosed_le hFc continuous_const)
    refine ⟨f,hfnz,hends,fun t ht ↦ ?_⟩
    exact sub_nonpos.mp (hcl (hretained ht))
  · have hcl : closure g'.openArc ⊆ {t | 0 ≤ F t} :=
      closure_minimal (fun t ht ↦ (show 0 < F t from hpos (mem_image_of_mem F ht)).le)
        (isClosed_le continuous_const hFc)
    refine ⟨-f,neg_ne_zero.mpr hfnz,by simpa using congrArg Neg.neg hends,fun t ht ↦ ?_⟩
    change -f (σ t) ≤ -f (σ g.first)
    exact neg_le_neg (sub_nonneg.mp (hcl (hretained ht)))

/-- Every chord of a complementary parameter arc lies on the frontier of the
retained contact hull. Its endpoints belong to the hull and the supporting
functional is constant on the chord. A nonzero functional is open, so a point
on its supporting level cannot be an interior point of the hull. -/
theorem cairns_gap_chord_subset_hull_frontier (σ : Circle → ℂ)
    (hσ : Continuous σ) (hinj : Function.Injective σ) (hnorm : ∀ t, ‖σ t‖ = 1)
    (S : Set Circle) (g : CairnsCircleGap) (hg : g.IsGapOf S) :
    segment ℝ (σ g.first) (σ g.last) ⊆ frontier (convexHull ℝ (σ '' S)) := by
  obtain ⟨f,hf,hends,hbound⟩ := cairns_gap_supporting_functional σ hσ hinj hnorm S g hg
  have hHull : convexHull ℝ (σ '' S) ⊆ {z | f z ≤ f (σ g.first)} := by
    apply convexHull_min
    · rintro z ⟨t,ht,rfl⟩
      exact hbound t ht
    · exact (convex_Iic _).linear_preimage f.toLinearMap
  intro z hz
  have hzHull : z ∈ convexHull ℝ (σ '' S) :=
    (convex_convexHull ℝ _).segment_subset
      (subset_convexHull ℝ _ (mem_image_of_mem σ hg.1))
      (subset_convexHull ℝ _ (mem_image_of_mem σ hg.2.1)) hz
  have hfz : f z = f (σ g.first) := by
    rw [segment_eq_image] at hz
    obtain ⟨t,ht,rfl⟩ := hz
    simp only [map_add,map_smul,smul_eq_mul,← hends]
    ring
  refine ⟨subset_closure hzHull,?_⟩
  intro hzint
  have hsub : f '' interior (convexHull ℝ (σ '' S)) ⊆ Iic (f (σ g.first)) := by
    rintro _ ⟨w,hw,rfl⟩
    exact hHull (interior_subset hw)
  have hmem := interior_maximal hsub (f.isOpenMap_of_ne_zero hf _ isOpen_interior)
    (mem_image_of_mem f hzint)
  rw [interior_Iic,hfz] at hmem
  exact lt_irrefl _ (show f (σ g.first) < f (σ g.first) from hmem)

/-- Retained unit-circle points themselves lie on the hull frontier, since the
whole hull lies in the closed disk and a circle point cannot be interior. -/
theorem circle_contact_subset_hull_frontier (S : Set ℂ)
    (hcircle : ∀ z ∈ S, ‖z‖ = 1) : S ⊆ frontier (convexHull ℝ S) := by
  have hsub : convexHull ℝ S ⊆ Metric.closedBall 0 1 := by
    apply convexHull_min
    · intro z hz
      simpa only [Metric.mem_closedBall,dist_zero_right,hcircle z hz] using (le_refl (1 : ℝ))
    · exact convex_closedBall (0 : ℂ) 1
  intro z hz
  refine ⟨subset_closure (subset_convexHull ℝ S hz),?_⟩
  intro hzint
  have hh := interior_mono hsub hzint
  rw [interior_closedBall (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] at hh
  have hh' : ‖z‖ < 1 := by simpa using hh
  rw [hcircle z hz] at hh'
  exact lt_irrefl _ hh'

/-- A bounded open target region with the prescribed contact-and-gap-chord
frontier is the interior of the contact hull, and hence an open disk. Every
listed frontier piece lies on the hull frontier by the supporting-chord lemma.
Boundedness then puts the region in the hull, and connectedness of the convex
interior gives equality. This is the convex target invariant in Cairns §4. -/
theorem cairns_contact_chord_region_eq_hull_interior {ι : Type*}
    (σ : Circle → ℂ) (hσ : Continuous σ) (hinj : Function.Injective σ)
    (hnorm : ∀ t, ‖σ t‖ = 1) (S : Set Circle) (hS : IsClosed S) (hSne : S.Nonempty)
    (gap : ι → CairnsCircleGap) (hgap : ∀ i, (gap i).IsGapOf S)
    (U : Set ℂ) (hU : IsOpen U) (hne : U.Nonempty) (hb : Bornology.IsBounded U)
    (hfront : frontier U ⊆ σ '' S ∪
      ⋃ i, segment ℝ (σ (gap i).first) (σ (gap i).last)) :
    U = interior (convexHull ℝ (σ '' S)) ∧
      Nonempty (U ≃ₜ Metric.ball (0 : ℂ) 1) ∧
      Nonempty (frontier U ≃ₜ Metric.sphere (0 : ℂ) 1) := by
  let C := convexHull ℝ (σ '' S)
  have hCcompact : IsCompact C :=
    isCompact_convexHull_finiteDimensional (hS.isCompact.image hσ)
  have hCne : C.Nonempty := (hSne.image σ).mono (subset_convexHull ℝ _)
  have hCconvex : Convex ℝ C := convex_convexHull ℝ _
  have hfrontC : frontier U ⊆ frontier C := by
    intro z hz
    rcases hfront hz with hz | hz
    · apply circle_contact_subset_hull_frontier _ (fun w hw ↦ ?_) hz
      obtain ⟨t,ht,rfl⟩ := hw
      exact hnorm t
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hz
      exact cairns_gap_chord_subset_hull_frontier σ hσ hinj hnorm S (gap i) (hgap i) hi
  have hsub : U ⊆ C := bounded_subset_closed_convex_of_frontier U C hb hCconvex
    hCcompact.isClosed hCne (hfrontC.trans (frontier_subset_iff_isClosed.mpr hCcompact.isClosed))
  exact ⟨open_eq_convex_interior_of_frontier_subset U C hU hne hsub hCconvex hfrontC,
    open_convex_body_disk_charts U C hU hne hsub hCconvex hCcompact.isBounded
      hCcompact.isClosed hfrontC⟩

end HolomorphicAnosov.Topology.Plane
