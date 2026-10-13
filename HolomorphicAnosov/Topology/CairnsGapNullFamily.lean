import HolomorphicAnosov.Topology.CairnsNormalizedCircleGap
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Sequences

namespace HolomorphicAnosov.Topology.Plane.CairnsCircleGap
open Set Filter MeasureTheory
open scoped _root_.Topology

/-- Shift an angular gap's interval to start at the principal argument of its
first endpoint. The image and interval length are unchanged. -/
theorem principal_interval_image (g : CairnsCircleGap) :
    Circle.exp '' Ioo (g.first : ℂ).arg
      ((g.first : ℂ).arg + (g.stop - g.start)) = g.openArc := by
  let a := (g.first : ℂ).arg
  have he : Circle.exp a = Circle.exp g.start := Circle.exp_arg g.first
  have hshift (t : ℝ) : Circle.exp (a + (t - g.start)) = Circle.exp t := by
    rw [Circle.exp_add, he, ← Circle.exp_add]
    congr 1
    ring
  change Circle.exp '' Ioo a (a + (g.stop - g.start)) = Circle.exp '' Ioo g.start g.stop
  ext z
  constructor
  · rintro ⟨t,ht,rfl⟩
    refine ⟨g.start + (t - a), ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    have hh := hshift (g.start + (t - a))
    convert hh.symm using 1; congr 1; ring
  · rintro ⟨t,ht,rfl⟩
    exact ⟨a + (t - g.start), ⟨by linarith [ht.1], by linarith [ht.2]⟩, hshift t⟩

/-- Shift an angular gap's interval to start at the principal argument of its
first endpoint. The image and interval length are unchanged. -/
theorem principal_closed_interval_image (g : CairnsCircleGap) :
    Circle.exp '' Icc (g.first : ℂ).arg
      ((g.first : ℂ).arg + (g.stop - g.start)) = g.closedArc := by
  let a := (g.first : ℂ).arg
  have he : Circle.exp a = Circle.exp g.start := Circle.exp_arg g.first
  have hshift (t : ℝ) : Circle.exp (a + (t - g.start)) = Circle.exp t := by
    rw [Circle.exp_add, he, ← Circle.exp_add]
    congr 1
    ring
  change Circle.exp '' Icc a (a + (g.stop - g.start)) = Circle.exp '' Icc g.start g.stop
  ext z
  constructor
  · rintro ⟨t,ht,rfl⟩
    refine ⟨g.start + (t - a), ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    have hh := hshift (g.start + (t - a))
    convert hh.symm using 1; congr 1; ring
  · rintro ⟨t,ht,rfl⟩
    exact ⟨a + (t - g.start), ⟨by linarith [ht.1], by linarith [ht.2]⟩, hshift t⟩

/-- Distinct disjoint proper angular gaps form a null family in angular
length. Source: Cairns (1951), §4(C), p.865. Move each angular interval into
(-π,3π); the intervals remain disjoint because their circle images are
disjoint. Their Lebesgue lengths are summable in this finite interval and
therefore tend to zero. -/
theorem length_tendsto_zero_of_disjoint
    {ι : Type*} (g : ι → CairnsCircleGap)
    (hdisj : Pairwise fun i j ↦ Disjoint (g i).openArc (g j).openArc)
    (j : ℕ → ι) (hj : Function.Injective j) :
    Tendsto (fun n ↦ (g (j n)).stop - (g (j n)).start) atTop (nhds 0) := by
  let a : ℕ → ℝ := fun n ↦ ((g (j n)).first : ℂ).arg
  let b : ℕ → ℝ := fun n ↦ a n + ((g (j n)).stop - (g (j n)).start)
  have hab (n) : a n < b n := by
    dsimp only [b]
    linarith [(g (j n)).start_lt_stop]
  have ha (n) : -Real.pi < a n := Complex.neg_pi_lt_arg _
  have hb (n) : b n < 3 * Real.pi := by
    dsimp only [b, a]
    linarith [(g (j n)).shorter_than_turn, Complex.arg_le_pi ((g (j n)).first : ℂ)]
  have himage (n) : Circle.exp '' Ioo (a n) (b n) = (g (j n)).openArc :=
    principal_interval_image _
  have hd : Pairwise fun n m ↦ Disjoint (Ioo (a n) (b n)) (Ioo (a m) (b m)) := by
    intro n m hnm
    apply Set.disjoint_left.mpr
    intro t htn htm
    exact Set.disjoint_left.mp (hdisj (fun he ↦ hnm (hj he)))
      (himage n ▸ mem_image_of_mem Circle.exp htn)
      (himage m ▸ mem_image_of_mem Circle.exp htm)
  let K : Set ℝ := Icc (-Real.pi) (3 * Real.pi)
  have hsub (n) : Ioo (a n) (b n) ⊆ K := fun t ht ↦
    ⟨(ha n).le.trans ht.1.le, ht.2.le.trans (hb n).le⟩
  let μ : Measure ℝ := volume.restrict K
  have hm (n) : μ.real (Ioo (a n) (b n)) = b n - a n := by
    dsimp only [μ, Measure.real]
    rw [Measure.restrict_apply measurableSet_Ioo, inter_eq_left.mpr (hsub n)]
    exact Real.volume_real_Ioo_of_le (hab n).le
  have hs : Summable (fun n ↦ b n - a n) := by
    have hh := summable_measure_toReal (μ := μ) (fun n ↦ measurableSet_Ioo) hd
    simpa only [hm] using hh
  simpa only [b, add_sub_cancel_left] using hs.tendsto_atTop_zero

/-- Under any continuous boundary parametrization the closed arcs of a
disjoint gap family have diameters tending to zero. Source: Cairns §4(C),
pp.864–865. Their principal angular intervals lie in the compact interval
[-π,3π] and their lengths tend to zero; uniform continuity converts this to
a uniform bound for every pair of image points. -/
theorem image_diam_tendsto_zero_of_disjoint
    {E ι : Type*} [PseudoMetricSpace E]
    (σ : Circle → E) (hσ : Continuous σ) (g : ι → CairnsCircleGap)
    (hdisj : Pairwise fun i j ↦ Disjoint (g i).openArc (g j).openArc)
    (j : ℕ → ι) (hj : Function.Injective j) :
    Tendsto (fun n ↦ Metric.diam (σ '' (g (j n)).closedArc)) atTop (nhds 0) := by
  let K : Set ℝ := Icc (-Real.pi) (3 * Real.pi)
  have huc : UniformContinuousOn (fun t ↦ σ (Circle.exp t)) K :=
    isCompact_Icc.uniformContinuousOn_of_continuous
      (hσ.comp Circle.exp.continuous).continuousOn
  have hl := length_tendsto_zero_of_disjoint g hdisj j hj
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hδspec⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / 2) (half_pos hε)
  filter_upwards [hl.eventually_lt_const hδ] with n hn
  have hdiam : Metric.diam (σ '' (g (j n)).closedArc) ≤ ε / 2 := by
    apply Metric.diam_le_of_forall_dist_le (half_pos hε).le
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    rw [← principal_closed_interval_image] at hx hy
    obtain ⟨u,hu,rfl⟩ := hx
    obtain ⟨v,hv,rfl⟩ := hy
    have hmem (t : ℝ)
        (ht : t ∈ Icc ((g (j n)).first : ℂ).arg
          (((g (j n)).first : ℂ).arg + ((g (j n)).stop - (g (j n)).start))) :
        t ∈ K := by
      constructor
      · linarith [Complex.neg_pi_lt_arg ((g (j n)).first : ℂ), ht.1]
      · linarith [(g (j n)).shorter_than_turn,
          Complex.arg_le_pi ((g (j n)).first : ℂ), ht.2]
    have huv : dist u v < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hu.1,hu.2,hv.1,hv.2]
    exact (hδspec u (hmem u hu) v (hmem v hv) huv).le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.diam_nonneg]
  exact hdiam.trans_lt (half_lt_self hε)

/-- Uniformly small angular gaps have uniformly small images under a
continuous boundary parametrization. This estimates every image point from
the first endpoint and is suitable for the sector closed-disk bound. -/
theorem small_gap_image_subset_ball
    {E : Type*} [PseudoMetricSpace E] (σ : Circle → E) (hσ : Continuous σ)
    (ε : ℝ) (hε : 0 < ε) : ∃ δ > 0, ∀ g : CairnsCircleGap,
      g.stop - g.start < δ → σ '' g.closedArc ⊆ Metric.ball (σ g.first) ε := by
  let K : Set ℝ := Icc (-Real.pi) (3 * Real.pi)
  have huc : UniformContinuousOn (fun t ↦ σ (Circle.exp t)) K :=
    isCompact_Icc.uniformContinuousOn_of_continuous
      (hσ.comp Circle.exp.continuous).continuousOn
  obtain ⟨δ,hδ,hδspec⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  refine ⟨δ,hδ,?_⟩
  intro g hgap z hz
  obtain ⟨t,ht,rfl⟩ := hz
  rw [← principal_closed_interval_image] at ht
  obtain ⟨θ,hθ,rfl⟩ := ht
  have ha : ((g.first : ℂ).arg) ∈ K :=
    ⟨(Complex.neg_pi_lt_arg _).le,by linarith [Complex.arg_le_pi (g.first : ℂ),Real.pi_pos]⟩
  have hθK : θ ∈ K := by
    constructor
    · exact ha.1.trans hθ.1
    · linarith [Complex.arg_le_pi (g.first : ℂ),g.shorter_than_turn,hθ.2]
  have hd : dist θ (g.first : ℂ).arg < δ := by
    rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hθ.1)]
    linarith [hθ.2]
  have hh := hδspec θ hθK (g.first : ℂ).arg ha hd
  simpa only [Circle.exp_arg,Metric.mem_ball] using hh

/-- Increasing contact sets with dense union have uniformly shrinking
angular gaps. Source: Cairns §4(C), the compactness step after Lemma 4.1.
Otherwise choose increasingly late gaps of a fixed positive minimum length.
Their principal starting angles have a convergent subsequence. A fixed open
interval inside the limiting initial part of those gaps contains a retained
contact by density, contradicting retention at every later stage. -/
theorem gap_length_eventually_lt_of_dense
    (T : ℕ → Set Circle) (hmono : Monotone T) (hdense : Dense (⋃ n, T n))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, ∀ g : CairnsCircleGap, g.IsGapOf (T n) → g.stop - g.start < ε := by
  classical
  by_contra! hbad
  choose j hj g hg hlength using hbad
  let a : ℕ → ℝ := fun n ↦ ((g n).first : ℂ).arg
  have ha (n : ℕ) : a n ∈ Icc (-Real.pi) Real.pi :=
    ⟨(Complex.neg_pi_lt_arg _).le,Complex.arg_le_pi _⟩
  obtain ⟨b,hb,k,hk,hlim⟩ := isCompact_Icc.tendsto_subseq ha
  let V : Set Circle := Circle.exp '' Ioo (b + ε / 3) (b + 2 * ε / 3)
  have hVopen : IsOpen V := isLocalHomeomorph_circleExp.isOpenMap _ isOpen_Ioo
  have hVne : V.Nonempty := (nonempty_Ioo.mpr (by linarith : b + ε / 3 < b + 2 * ε / 3)).image _
  obtain ⟨z,hzU,hzV⟩ := hdense.exists_mem_open hVopen hVne
  obtain ⟨N,hzN⟩ := mem_iUnion.mp hzU
  obtain ⟨θ,hθ,rfl⟩ := hzV
  have hevent : ∀ᶠ n in atTop, b - ε / 3 < a (k n) ∧ a (k n) < b + ε / 3 ∧ N ≤ j (k n) := by
    filter_upwards [hlim.eventually_const_lt (by linarith : b - ε / 3 < b),
      hlim.eventually_lt_const (by linarith : b < b + ε / 3),
      eventually_ge_atTop N] with n hnlo hnhi hnN
    exact ⟨hnlo,hnhi,hnN.trans ((hk.id_le n).trans (hj (k n)))⟩
  obtain ⟨n,hnlo,hnhi,hnN⟩ := hevent.exists
  have hzarc : Circle.exp θ ∈ (g (k n)).openArc := by
    rw [← principal_interval_image]
    refine ⟨θ,⟨?_,?_⟩,rfl⟩
    · change a (k n) < θ
      linarith [hθ.1]
    · change θ < a (k n) + ((g (k n)).stop - (g (k n)).start)
      linarith [hθ.2,hlength (k n)]
  obtain ⟨x,hx,hcomp⟩ := (hg (k n)).2.2
  have hznot : Circle.exp θ ∉ T (j (k n)) := by
    apply connectedComponentIn_subset (T (j (k n)))ᶜ x
    rw [hcomp]
    exact hzarc
  exact hznot (hmono hnN hzN)

/-- Cairns's literal normalized supremum mesh tends to zero once increasing
contacts are dense. Zero is included in the supremum, so this statement also
covers stages having no residual gaps. -/
theorem mesh_tendsto_zero_of_dense
    (T : ℕ → Set Circle) (hmono : Monotone T) (hdense : Dense (⋃ n, T n)) :
    Tendsto (fun n ↦ mesh (T n)) atTop (nhds 0) := by
  have hturn : 0 < 2 * Real.pi := by positivity
  have hbounded (n : ℕ) : BddAbove (insert 0 (normalizedLength '' {g | g.IsGapOf (T n)})) := by
    refine ⟨1,?_⟩
    rintro x (rfl | ⟨g,hg,rfl⟩)
    · norm_num
    · exact ((div_lt_one hturn).mpr g.shorter_than_turn).le
  have hnonneg (n : ℕ) : 0 ≤ mesh (T n) := le_csSup (hbounded n) (mem_insert _ _)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := gap_length_eventually_lt_of_dense T hmono hdense
    ((ε / 2) * (2 * Real.pi)) (mul_pos (half_pos hε) hturn)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hm : mesh (T n) ≤ ε / 2 := by
    apply csSup_le ⟨0,mem_insert _ _⟩
    rintro x (rfl | ⟨g,hg,rfl⟩)
    · exact (half_pos hε).le
    · exact ((div_lt_iff₀ hturn).mpr (hN n hn g hg)).le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnonneg n)]
  exact hm.trans_lt (half_lt_self hε)

end HolomorphicAnosov.Topology.Plane.CairnsCircleGap



