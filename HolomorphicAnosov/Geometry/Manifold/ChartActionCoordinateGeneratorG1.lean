import HolomorphicAnosov.Geometry.Manifold.ActionChartAverageInvertibleG1
import HolomorphicAnosov.Geometry.Manifold.AverageMapSmoothFromJetsG1
import HolomorphicAnosov.Geometry.Manifold.SmoothInvertibleDerivativeNeighborhoodG1
import HolomorphicAnosov.Geometry.Manifold.LocalSmoothGeneratorFromAverageG1

open scoped Manifold ContDiff Interval Topology _root_.Topology
open Function Set Filter MeasureTheory
noncomputable section
namespace HolomorphicAnosov

/-- The time-averaged action map is smooth near a chart center and its derivative yields a smooth local coordinate generator. (Bochner–Montgomery, Lemmas 2 and 5.) -/
theorem chart_action_coordinate_generator_g1
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (a : ℝ → M → M) (hcont : Continuous (Function.uncurry a))
    (hzero : ∀ x, a 0 x = x)
    (hadd : ∀ s t x, a s (a t x) = a (s+t) x)
    (hdiff : ∀ t, ∃ g : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞, ∀ x, g x = a t x)
    (x : M) (r : ℝ) (hr : 0 < r)
    (haverage : ∀ h : ℝ, 0 ≤ h → h ≤ r/2 →
      ∀ y ∈ Metric.ball (chartAt E x x) (r/2), ∀ k : ℕ,
        HasFDerivAt
          (fun z ↦ ∫ t in 0..h, iteratedFDeriv ℝ k
            (fun w : E ↦ chartAt E x (a t ((chartAt E x).symm w))) z)
          (∫ t in 0..h, fderiv ℝ (iteratedFDeriv ℝ k
            (fun w : E ↦ chartAt E x (a t ((chartAt E x).symm w)))) y) y) :
    ∃ W : Set E, IsOpen W ∧ chartAt E x x ∈ W ∧ W ⊆ (chartAt E x).target ∧
      ∃ X : E → E, ContDiffOn ℝ ∞ X W ∧
        ∀ y ∈ W, HasDerivAt
          (fun t : ℝ ↦ chartAt E x (a t ((chartAt E x).symm y))) (X y) 0 := by
  let : AddAction ℝ M :=
    { vadd := a
      zero_vadd := hzero
      add_vadd := fun s t x ↦ (hadd s t x).symm }
  let : ContinuousVAdd ℝ M := ⟨hcont⟩
  have hsmooth : ∀ t : ℝ, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (fun x : M ↦ t +ᵥ x) := by
    intro t
    obtain ⟨g, hg⟩ := hdiff t
    have heq : (fun x : M ↦ t +ᵥ x) = g := funext (fun x ↦ (hg x).symm)
    rw [heq]
    exact g.contMDiff
  let e := chartAt E x
  have hx : x ∈ e.source := mem_chart_source E x
  have hext : e x ∈ e.target := e.map_source hx
  have h₀ : (0 : ℝ) +ᵥ e.symm (e x) ∈ e.source := by
    simpa only [zero_vadd, e.left_inv hx] using hx
  obtain ⟨δ, hδ, hdom⟩ :=
    VectorActionSpatialSupport.exists_action_coordinate_product e e 0 (e x) hext h₀
  obtain ⟨h, hh, hhR, B, hB⟩ := action_chart_average_invertible_g1
    a hcont hzero hadd hdiff x (min (r/2) δ) (lt_min (half_pos hr) hδ)
  have hhr : h < r/2 := lt_of_lt_of_le hhR (min_le_left _ _)
  have hhδ : h < δ := lt_of_lt_of_le hhR (min_le_right _ _)
  have hht : h ∈ Metric.ball (0 : ℝ) δ := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hh] using hhδ
  have h0t : (0 : ℝ) ∈ Metric.ball (0 : ℝ) δ := Metric.mem_ball_self hδ
  let f := fun t : ℝ ↦ fun y : E ↦ e (a t (e.symm y))
  let S := Metric.ball (e x) (r/2) ∩ Metric.ball (e x) δ
  have hS : IsOpen S := Metric.isOpen_ball.inter Metric.isOpen_ball
  have hxS : e x ∈ S := ⟨Metric.mem_ball_self (half_pos hr), Metric.mem_ball_self hδ⟩
  obtain ⟨hA, hDA⟩ := average_map_smooth_from_jets_g1 f h S
    (fun y hy k ↦ haverage h hh.le hhr.le y hy.1 k)
  have hDB : HasFDerivAt (fun y ↦ ∫ t in 0..h, f t y) B.toContinuousLinearMap (e x) := by
    simpa only [hB] using hDA (e x) (hS.mem_nhds hxS)
  obtain ⟨W, hWo, hxW, hWS, C, hC, hDC⟩ :=
    smooth_invertible_derivative_neighborhood_g1 (fun y ↦ ∫ t in 0..h, f t y)
      S hS (e x) hxS hA B hDB
  have htarget : ∀ y ∈ W, y ∈ e.target := fun y hy ↦ (hdom 0 h0t y (hWS hy).2).1
  have hct : ∀ y ∈ W, ∀ t ∈ Metric.ball (0 : ℝ) δ,
      ContinuousAt (fun s ↦ f s y) t := by
    intro y hy t ht
    have hc : ContinuousAt (fun s : ℝ ↦ a s (e.symm y)) t :=
      (hcont.comp (continuous_id.prodMk continuous_const)).continuousAt
    exact (e.continuousAt (hdom t ht y (hWS hy).2).2).comp_of_eq hc rfl
  have hcm : ∀ y ∈ W, ContinuousOn (fun t ↦ f t y) (Metric.ball (0 : ℝ) δ) :=
    fun y hy t ht ↦ (hct y hy t ht).continuousWithinAt
  have hinterval : Set.uIcc (0 : ℝ) h ⊆ Metric.ball (0 : ℝ) δ := by
    intro t ht
    rw [uIcc_of_le hh.le] at ht
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1] using
      lt_of_le_of_lt ht.2 hhδ
  have hfzero : ∀ y ∈ W, f 0 y = y := by
    intro y hy
    dsimp [f]
    rw [hzero, e.right_inv (htarget y hy)]
  have hslice : ContDiffOn ℝ ∞ (f h) W := by
    intro y hy
    exact (VectorActionSpatialSupport.action_coordinate_contDiffAt hsmooth e e
      (IsManifold.chart_mem_maximalAtlas x) (IsManifold.chart_mem_maximalAtlas x)
      h y (htarget y hy) (hdom h hht y (hWS hy).2).2).contDiffWithinAt
  have hcomp : ∀ y ∈ W, ∀ᶠ p in 𝓝 (0 : ℝ), ∀ t ∈ Set.uIcc 0 h,
      f t (f p y) = f (t+p) y := by
    intro y hy
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with p hp
    intro t ht
    dsimp [f]
    have hpdom : a p (e.symm y) ∈ e.source := (hdom p hp y (hWS hy).2).2
    rw [e.left_inv hpdom, hadd]
  obtain ⟨hX, hdX⟩ := local_smooth_generator_from_average_g1 f W h C hfzero hC hslice
    (fun y hy ↦ ((hcm y hy).mono hinterval).intervalIntegrable)
    (fun y hy ↦ (hcm y hy).stronglyMeasurableAtFilter Metric.isOpen_ball 0 h0t)
    (fun y hy ↦ (hcm y hy).stronglyMeasurableAtFilter Metric.isOpen_ball h hht)
    (fun y hy ↦ hct y hy 0 h0t) (fun y hy ↦ hct y hy h hht) hDC hcomp
  exact ⟨W, hWo, hxW, htarget, _, hX, hdX⟩

end HolomorphicAnosov
