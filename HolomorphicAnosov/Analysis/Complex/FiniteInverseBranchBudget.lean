import HolomorphicAnosov.Analysis.Complex.HolomorphicInverseWeightedArea
import HolomorphicAnosov.Analysis.Complex.HolomorphicBijOnInverse
import HolomorphicAnosov.Topology.CompactLocalInjectiveBranches

/-! # Finite inverse branch area budgets

Source: the original local-cover proof of Ghys Proposition 4.1, §4 pp.594–597,
assembled from holomorphic change of variables and finite disjoint measurable
ownership. Compact source cores supply finite inverse charts; overlapping
image sets retain one weight for each actual source root. All compact-core,
measurability, nonvanishing derivative, and finite-budget hypotheses remain
explicit. Empty cores and infinite nonnegative source weights are allowed.
-/


open Set MeasureTheory
open scoped ENNReal _root_.Topology
namespace HolomorphicAnosov.Analysis.Complex

/-- Measurable ownership pieces in a holomorphic local inverse chart have
measurable images and measurable inverse-Jacobian densities. The image is
Borel by injectivity and continuity on a Borel subset of the complex plane.
On that image the inverse and the forward derivative are continuous and the
derivative is nonzero, so the real reciprocal squared norm is continuous.
Extend the density by zero across the Borel image to obtain measurability. -/
theorem holomorphic_inverse_chart_density_measurable
    (e : OpenPartialHomeomorph ℂ ℂ)
    (he : DifferentiableOn ℂ e e.source)
    (hne : ∀ z ∈ e.source, deriv e z ≠ 0)
    (P : Set ℂ) (hP : MeasurableSet P) (hPe : P ⊆ e.source) (C : ℝ) :
    MeasurableSet (e '' P) ∧ Measurable ((e '' P).indicator
      (fun y ↦ ENNReal.ofReal C / ENNReal.ofReal (‖deriv e (e.symm y)‖ ^ 2))) := by
  classical
  have himage : MeasurableSet (e '' P) :=
    hP.image_of_continuousOn_injOn (e.continuousOn.mono hPe) (e.injOn.mono hPe)
  have htarget : e '' P ⊆ e.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact e.map_source (hPe hz)
  have hinv : Set.MapsTo e.symm (e '' P) e.source :=
    fun y hy ↦ e.map_target (htarget hy)
  have hd : ContinuousOn (fun y ↦ deriv e (e.symm y)) (e '' P) :=
    (he.deriv e.open_source).continuousOn.comp (e.symm.continuousOn.mono htarget) hinv
  have hpos (y : ℂ) (hy : y ∈ e '' P) : 0 < ‖deriv e (e.symm y)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (hne _ (hinv hy)))
  have hc : ContinuousOn (fun y ↦ ENNReal.ofReal C /
      ENNReal.ofReal (‖deriv e (e.symm y)‖ ^ 2)) (e '' P) := by
    have hr : ContinuousOn (fun y ↦ C / ‖deriv e (e.symm y)‖ ^ 2) (e '' P) :=
      continuousOn_const.div (hd.norm.pow 2) (fun y hy ↦ (hpos y hy).ne')
    apply (ENNReal.continuous_ofReal.comp_continuousOn hr).congr
    intro y hy
    exact (ENNReal.ofReal_div_of_pos (hpos y hy)).symm
  refine ⟨himage, ?_⟩
  exact hc.measurable_piecewise continuousOn_const himage

/-- Disjoint source ownership counts each actual root exactly once, even if
branch images overlap. Restrict to the active branches over y. Their inverse
points belong to their ownership pieces; disjointness makes this assignment
injective, and coverage of the root set makes it surjective. Reindex the finite
sum by that bijection. No uniform bound on fiber cardinalities is used. -/
theorem inverse_branch_density_eq_root_sum
    {ι X Y : Type*} [Fintype ι] [DecidableEq X]
    (g : X → Y) (P : ι → Set X)
    (hdisj : Pairwise (fun i j ↦ Disjoint (P i) (P j)))
    (inv : ι → Y → X) (hleft : ∀ i x, x ∈ P i → inv i (g x) = x)
    (w : X → ℝ≥0∞) (y : Y) (roots : Finset X)
    (hroots : ∀ x, x ∈ roots ↔ x ∈ ⋃ i, P i ∧ g x = y) :
    ∑ i, (g '' P i).indicator (fun z ↦ w (inv i z)) y =
      ∑ x ∈ roots, w x := by
  classical
  let active : Finset ι := Finset.univ.filter (fun i ↦ y ∈ g '' P i)
  have hmem (i : ι) (hi : i ∈ active) : inv i y ∈ P i ∧ g (inv i y) = y := by
    obtain ⟨x,hx,hxy⟩ := (Finset.mem_filter.mp hi).2
    subst y
    rw [hleft i x hx]
    exact ⟨hx,rfl⟩
  have hsum : (∑ i, (g '' P i).indicator (fun z ↦ w (inv i z)) y) =
      ∑ i ∈ active, w (inv i y) := by
    simp only [active, Finset.sum_filter, Set.indicator_apply]
  rw [hsum]
  apply Finset.sum_bij (fun i _ ↦ inv i y)
  · intro i hi
    exact (hroots _).mpr ⟨Set.mem_iUnion.mpr ⟨i,(hmem i hi).1⟩,(hmem i hi).2⟩
  · intro i hi j hj heq
    by_contra hij
    exact Set.disjoint_left.mp (hdisj hij) (hmem i hi).1 (heq ▸ (hmem j hj).1)
  · intro x hx
    obtain ⟨hxP,hxy⟩ := (hroots x).mp hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hxP
    refine ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨x,hi,hxy⟩⟩,?_⟩
    rw [← hxy,hleft i x hi]
  · intro i hi
    rfl

/-- Finite disjoint source ownership gives an exact integral identity for the
sum of inverse-derivative branch weights, even when target images overlap.

For each branch, measurable extension by zero converts its whole-plane integral
to the image integral. Holomorphic change of variables cancels the squared
complex derivative. Finite additivity on the disjoint measurable source pieces
then gives the integral on their union. This is the analytic budget step of
the agent-written Markov-free proof of Ghys Proposition 4.1. Image and density
measurability are retained explicitly; local inverse charts provide them in
the geometric application. No bound on the number of branches is required. -/
theorem finite_inverse_branch_budget
    {ι : Type*} [Fintype ι]
    (U : Set ℂ) (hU : IsOpen U) (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g U)
    (P : ι → Set ℂ) (hP : ∀ i, MeasurableSet (P i))
    (hPU : ∀ i, P i ⊆ U) (hdisj : Pairwise (fun i j ↦ Disjoint (P i) (P j)))
    (inv : ι → ℂ → ℂ) (hleft : ∀ i z, z ∈ P i → inv i (g z) = z)
    (hnz : ∀ i z, z ∈ P i → deriv g z ≠ 0)
    (w : ℂ → ℝ≥0∞) (himage : ∀ i, MeasurableSet (g '' P i))
    (hmeas : ∀ i, Measurable ((g '' P i).indicator
      (fun y ↦ w (inv i y) / ENNReal.ofReal (‖deriv g (inv i y)‖ ^ 2)))) :
    (∫⁻ y, ∑ i, (g '' P i).indicator
      (fun y ↦ w (inv i y) / ENNReal.ofReal (‖deriv g (inv i y)‖ ^ 2)) y ∂volume) =
      ∫⁻ z in ⋃ i, P i, w z ∂volume := by
  classical
  rw [lintegral_finsetSum _ (fun i _ ↦ hmeas i)]
  simp_rw [lintegral_indicator (himage _)]
  simp_rw [lintegral_image_inverse_deriv_weight hU (hP _) (hPU _) hg (hleft _) (hnz _) w]
  rw [lintegral_iUnion hP hdisj w, tsum_fintype]

/-- Restricting the target only decreases the inverse-branch budget, and the
disjoint source pieces may be bounded by any encompassing source core. This
is the inequality form used for a fixed receiving disc. -/
theorem finite_inverse_branch_budget_le
    {ι : Type*} [Fintype ι]
    (U : Set ℂ) (hU : IsOpen U) (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g U)
    (P : ι → Set ℂ) (hP : ∀ i, MeasurableSet (P i))
    (hPU : ∀ i, P i ⊆ U) (hdisj : Pairwise (fun i j ↦ Disjoint (P i) (P j)))
    (inv : ι → ℂ → ℂ) (hleft : ∀ i z, z ∈ P i → inv i (g z) = z)
    (hnz : ∀ i z, z ∈ P i → deriv g z ≠ 0)
    (w : ℂ → ℝ≥0∞) (himage : ∀ i, MeasurableSet (g '' P i))
    (hmeas : ∀ i, Measurable ((g '' P i).indicator
      (fun y ↦ w (inv i y) / ENNReal.ofReal (‖deriv g (inv i y)‖ ^ 2))))
    (T K : Set ℂ) (hPK : ∀ i, P i ⊆ K) :
    (∫⁻ y in T, ∑ i, (g '' P i).indicator
      (fun y ↦ w (inv i y) / ENNReal.ofReal (‖deriv g (inv i y)‖ ^ 2)) y ∂volume) ≤
      ∫⁻ z in K, w z ∂volume := by
  calc
    _ ≤ ∫⁻ y, ∑ i, (g '' P i).indicator
      (fun y ↦ w (inv i y) / ENNReal.ofReal (‖deriv g (inv i y)‖ ^ 2)) y ∂volume :=
      setLIntegral_le_lintegral _ _
    _ = ∫⁻ z in ⋃ i, P i, w z ∂volume :=
      finite_inverse_branch_budget U hU g hg P hP hPU hdisj inv hleft hnz w himage hmeas
    _ ≤ ∫⁻ z in K, w z ∂volume := lintegral_mono_set (iUnion_subset hPK)

/-- Compact locally injective holomorphic cores have a measurable root density
with the exact constant-weight area budget. The proof constructs the finite
Borel ownership and inverse branches; those are conclusions, not assumptions. -/
theorem compact_holomorphic_root_density_budget
    (U K : Set ℂ) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g U)
    (hnz : ∀ z ∈ K, deriv g z ≠ 0)
    (C : ℝ≥0∞) :
    ∃ B : ℂ → ℝ≥0∞, Measurable B ∧
      (∫⁻ y, B y ∂volume) = C * volume K ∧
      (∀ y, (K ∩ g ⁻¹' {y}).Finite) ∧
      ∀ y (roots : Finset ℂ), (∀ z, z ∈ roots ↔ z ∈ K ∧ g z = y) →
        B y = ∑ z ∈ roots, C / ENNReal.ofReal (‖deriv g z‖ ^ 2) := by
  classical
  have hlocal : ∀ z ∈ K, ∃ V, IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧ V.InjOn g := by
    intro z hz
    have ha : AnalyticAt ℂ g z := hg.analyticOnNhd hU z (hKU hz)
    let inv := ha.hasStrictDerivAt.localInverse g (deriv g z) z (hnz z hz)
    have hi : ∀ᶠ w in 𝓝 z, inv (g w) = w :=
      ha.hasStrictDerivAt.eventually_left_inverse (hnz z hz)
    obtain ⟨V,hVsub,hVo,hzV⟩ := mem_nhds_iff.mp (hi.and (hU.mem_nhds (hKU hz)))
    refine ⟨V,hVo,hzV,fun w hw ↦ (hVsub hw).2,?_⟩
    intro x hx y hy hxy
    exact (hVsub hx).1.symm.trans ((congrArg inv hxy).trans (hVsub hy).1)
  obtain ⟨n,V,hV,hcover⟩ := compact_local_injective_cover K U g hK hlocal
  obtain ⟨P,hP,hdisj,hunion⟩ := finite_measurable_cover_ownership K hK.measurableSet
    V (fun i ↦ (hV i).1.measurableSet) hcover
  have hex (i : Fin n) : ∃ inv : ℂ → ℂ,
      DifferentiableOn ℂ inv (g '' V i) ∧ MapsTo inv (g '' V i) (V i) ∧
      (∀ z ∈ V i, inv (g z) = z) ∧ (∀ y ∈ g '' V i, g (inv y) = y) :=
    holomorphic_bijOn_inverse (hV i).1 (hg.mono (hV i).2.1) (hV i).2.2.bijOn_image
  choose inv hdinv hmap hleft hright using hex
  have hPU (i) : P i ⊆ U := fun z hz ↦ hKU ((hP i).2 hz).1
  have himage (i) : MeasurableSet (g '' P i) :=
    (hP i).1.image_of_continuousOn_injOn (hg.continuousOn.mono (hPU i))
      ((hV i).2.2.mono (fun z hz ↦ ((hP i).2 hz).2))
  have hmeas (i) : Measurable ((g '' P i).indicator
      (fun y ↦ C / ENNReal.ofReal (‖deriv g (inv i y)‖ ^ 2))) := by
    have hsub : g '' P i ⊆ g '' V i := image_mono (fun z hz ↦ ((hP i).2 hz).2)
    have hin (y) (hy : y ∈ g '' P i) : inv i y ∈ K := by
      obtain ⟨z,hz,rfl⟩ := hy
      rw [hleft i z ((hP i).2 hz).2]
      exact ((hP i).2 hz).1
    have hd : ContinuousOn (fun y ↦ deriv g (inv i y)) (g '' P i) :=
      (hg.deriv hU).continuousOn.comp ((hdinv i).continuousOn.mono hsub)
        (fun y hy ↦ hKU (hin y hy))
    have hden : ContinuousOn (fun y ↦ ENNReal.ofReal (‖deriv g (inv i y)‖ ^ 2))
        (g '' P i) := ENNReal.continuous_ofReal.comp_continuousOn (hd.norm.pow 2)
    have hc : ContinuousOn (fun y ↦ C / ENNReal.ofReal (‖deriv g (inv i y)‖ ^ 2))
        (g '' P i) := by
      simp only [div_eq_mul_inv]
      apply continuousOn_const.ennreal_mul
        ((continuous_inv : Continuous (Inv.inv : ℝ≥0∞ → ℝ≥0∞)).comp_continuousOn hden)
      · intro y hy
        exact Or.inr (by simpa using (ne_of_gt (ENNReal.ofReal_pos.mpr
          (sq_pos_of_pos (norm_pos_iff.mpr (hnz _ (hin y hy)))))))
      · intro y hy
        exact Or.inl (by simp)
    exact hc.measurable_piecewise continuousOn_const (himage i)
  let B : ℂ → ℝ≥0∞ := fun y ↦ ∑ i,
    (g '' P i).indicator (fun y ↦ C / ENNReal.ofReal (‖deriv g (inv i y)‖ ^ 2)) y
  refine ⟨B,Finset.measurable_sum _ (fun i _ ↦ hmeas i),?_,
    compact_local_injective_fiber_finite K U g hK hlocal,?_⟩
  · have h := finite_inverse_branch_budget U hU g hg P (fun i ↦ (hP i).1) hPU hdisj inv
      (fun i z hz ↦ hleft i z ((hP i).2 hz).2)
      (fun i z hz ↦ hnz z ((hP i).2 hz).1) (fun _ ↦ C) himage hmeas
    simpa only [hunion,setLIntegral_const] using h
  · intro y roots hroots
    exact inverse_branch_density_eq_root_sum g P hdisj inv
      (fun i z hz ↦ hleft i z ((hP i).2 hz).2)
      (fun z ↦ C / ENNReal.ofReal (‖deriv g z‖ ^ 2)) y roots
      (fun z ↦ by simpa only [hunion] using hroots z)

/-- An injective source coordinate transports the compact-core density back to
the literal source roots. Enlarging the source core gives a budget independent
of the particular compact root restriction. No change of measure on the
abstract source is used: the budget is the planar area of its coordinate image. -/
theorem compact_coordinate_root_density_budget
    {X : Type*} [TopologicalSpace X]
    (χ : X → ℂ) (hχ : Continuous χ) (hinj : Function.Injective χ)
    (R K : Set X) (hR : IsCompact R) (hRK : R ⊆ K)
    (U : Set ℂ) (hU : IsOpen U) (hRU : χ '' R ⊆ U)
    (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g U)
    (hnz : ∀ x ∈ R, deriv g (χ x) ≠ 0) (C : ℝ≥0∞) :
    ∃ B : ℂ → ℝ≥0∞, Measurable B ∧
      (∫⁻ y, B y ∂volume) ≤ C * volume (χ '' K) ∧
      (∀ y, {x ∈ R | g (χ x) = y}.Finite) ∧
      ∀ y (roots : Finset X), (∀ x, x ∈ roots ↔ x ∈ R ∧ g (χ x) = y) →
        B y = ∑ x ∈ roots, C / ENNReal.ofReal (‖deriv g (χ x)‖ ^ 2) := by
  classical
  obtain ⟨B,hB,hbudget,hfinite,hroot⟩ := compact_holomorphic_root_density_budget
    U (χ '' R) hU (hR.image hχ) hRU g hg
    (by rintro z ⟨x,hx,rfl⟩; exact hnz x hx) C
  refine ⟨B,hB,hbudget.le.trans (mul_le_mul_right (measure_mono (image_mono hRK)) C),?_,?_⟩
  · intro y
    have hf := (hfinite y).preimage hinj.injOn
    exact hf.subset (by intro x hx; exact ⟨mem_image_of_mem χ hx.1,hx.2⟩)
  · intro y roots hroots
    have hr : ∀ z, z ∈ roots.image χ ↔ z ∈ χ '' R ∧ g z = y := by
      intro z
      constructor
      · intro hz
        obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
        exact ⟨mem_image_of_mem χ ((hroots x).mp hx).1,((hroots x).mp hx).2⟩
      · rintro ⟨⟨x,hx,rfl⟩,hy⟩
        exact Finset.mem_image.mpr ⟨x,(hroots x).mpr ⟨hx,hy⟩,rfl⟩
    rw [hroot y (roots.image χ) hr]
    exact Finset.sum_image (fun x _ x' _ h ↦ hinj h)



/-- A fixed finite integral budget cannot dominate arbitrarily many copies of
a positive gap on a set of positive measure. Integrate the pointwise lower
bound and choose an integer multiple of the positive gap times measure larger
than the budget. The density may change with the integer, exactly as the
iterate is chosen after the number of paths in the Proposition 4.1 argument. -/
theorem finite_integral_budget_excludes_packing
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (T : Set X) (hT : MeasurableSet T) (hμT : μ T ≠ 0)
    (gap budget : ℝ≥0∞) (hgap : gap ≠ 0) (hbudget : budget ≠ ∞)
    (hpacking : ∀ n : ℕ, ∃ B : X → ℝ≥0∞,
      (∫⁻ x in T, B x ∂μ) ≤ budget ∧ ∀ x ∈ T, (n : ℝ≥0∞) * gap ≤ B x) :
    False := by
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt (mul_ne_zero hgap hμT) hbudget
  obtain ⟨B, hB, hpoint⟩ := hpacking n
  have hlow : (n : ℝ≥0∞) * (gap * μ T) ≤ ∫⁻ x in T, B x ∂μ := by
    simpa only [setLIntegral_const, mul_assoc] using
      (setLIntegral_mono' hT hpoint :
        (∫⁻ _x in T, (n : ℝ≥0∞) * gap ∂μ) ≤ ∫⁻ x in T, B x ∂μ)
  exact (not_lt_of_ge (hlow.trans hB)) hn

end HolomorphicAnosov.Analysis.Complex
