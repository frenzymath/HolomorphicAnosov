import HolomorphicAnosov.Geometry.Manifold.CompactParameterIntegralDerivative
import HolomorphicAnosov.Geometry.Manifold.LocalActionGeneratorFromAverage
import HolomorphicAnosov.Geometry.Manifold.OneParameterSmoothGeneratorLocalAssembly
import HolomorphicAnosov.Geometry.Manifold.VectorActionSpatialDerivativesContinuous
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
A jointly continuous additive real action whose time slices are smooth diffeomorphisms has a
smooth infinitesimal generator. (Bochner–Montgomery, Lemmas 2 and 5)
-/

open scoped Manifold ContDiff
open Function Set

noncomputable section

namespace HolomorphicAnosov

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

omit [TopologicalSpace M] in
/-- Each time slice of an additive action with identity at time zero has the opposite-time slice as
its two-sided inverse. (Bochner–Montgomery, Lemma 2) -/
theorem one_parameter_action_inverse
    (a : ℝ → M → M) (hzero : ∀ x, a 0 x = x)
    (hadd : ∀ s t x, a s (a t x) = a (s + t) x) (t : ℝ) (x : M) :
    a (-t) (a t x) = x ∧ a t (a (-t) x) = x := by
  constructor
  · rw [hadd, neg_add_cancel, hzero]
  · rw [hadd, add_neg_cancel, hzero]

omit [TopologicalSpace M] in
/-- Each time slice of an additive action with identity at time zero is bijective. -/
theorem one_parameter_action_bijective
    (a : ℝ → M → M) (hzero : ∀ x, a 0 x = x)
    (hadd : ∀ s t x, a s (a t x) = a (s + t) x) (t : ℝ) :
    Function.Bijective (a t) := by
  have hinv := one_parameter_action_inverse a hzero hadd t
  constructor
  · intro x y hxy
    have hinv_x := one_parameter_action_inverse a hzero hadd t x
    have hinv_y := one_parameter_action_inverse a hzero hadd t y
    calc
      x = a (-t) (a t x) := hinv_x.1.symm
      _ = a (-t) (a t y) := congrArg (a (-t)) hxy
      _ = y := hinv_y.1
  · intro y
    have hinv_y := one_parameter_action_inverse a hzero hadd t y
    refine ⟨a (-t) y, ?_⟩
    exact hinv_y.2

omit [TopologicalSpace M] in
/-- The opposite-time slice is a left and right inverse of the time-`t` slice. -/
theorem one_parameter_action_leftInverse_rightInverse
    (a : ℝ → M → M) (hzero : ∀ x, a 0 x = x)
    (hadd : ∀ s t x, a s (a t x) = a (s + t) x) (t : ℝ) :
    Function.LeftInverse (a (-t)) (a t) ∧ Function.RightInverse (a (-t)) (a t) := by
  constructor
  · intro x
    exact (one_parameter_action_inverse a hzero hadd t x).1
  · intro x
    exact (one_parameter_action_inverse a hzero hadd t x).2

/-- A jointly continuous additive real action whose time slices are smooth diffeomorphisms has orbit
derivatives at zero forming a smooth tangent section. (Bochner–Montgomery, Lemmas 2 and 5, pp.
687–689, 691) -/
theorem one_parameter_smooth_generator
    (a : ℝ → M → M)
    (hcont : Continuous (Function.uncurry a))
    (hzero : ∀ x, a 0 x = x)
    (hadd : ∀ s t x, a s (a t x) = a (s + t) x)
    (hdiff : ∀ t, ∃ g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ x, g x = a t x) :
    ∃ X : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      CMDiff ∞ (T% X) ∧
        ∀ x, ∃ L : TangentSpace 𝓘(ℝ, ℝ) 0 →L[ℝ] TangentSpace 𝓘(ℝ, E) (a 0 x),
          HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun t : ℝ ↦ a t x) 0 L ∧
            X x = tangentSpaceCast (𝓘(ℝ, E)) (a 0 x) x
              (L ((tangentSpaceCastModel (𝓘(ℝ, ℝ)) 0).symm 1)) := by
  let : AddAction ℝ M :=
    { vadd := a
      zero_vadd := hzero
      add_vadd := fun s t x ↦ (hadd s t x).symm }
  let : ContinuousVAdd ℝ M := ⟨hcont⟩
  have hsmooth : ∀ t : ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun x : M ↦ t +ᵥ x) := by
    intro t
    obtain ⟨g, hg⟩ := hdiff t
    have heq : (fun x : M ↦ t +ᵥ x) = g := funext (fun x ↦ (hg x).symm)
    rw [heq]
    exact g.contMDiff
  
  
  have hlocal (x : M) :
      ∃ r > 0,
        (∀ t ∈ Metric.ball (0 : ℝ) r, ∀ y ∈ Metric.ball (chartAt E x x) r,
          y ∈ (chartAt E x).target ∧ a t ((chartAt E x).symm y) ∈ (chartAt E x).source) ∧
        (∀ k : ℕ, ContinuousOn
          (fun p : ℝ × E ↦ iteratedFDeriv ℝ k
            (fun y : E ↦ chartAt E x (a p.1 ((chartAt E x).symm y))) p.2)
          (Metric.ball (0 : ℝ) r ×ˢ Metric.ball (chartAt E x x) r)) ∧
        (∀ y ∈ Metric.ball (chartAt E x x) r,
          HasFDerivAt (fun z : E ↦ chartAt E x (a 0 ((chartAt E x).symm z)))
            (ContinuousLinearMap.id ℝ E) y) ∧
        (∀ k : ℕ, ∃ C : ℝ,
          ∀ t ∈ Metric.closedBall (0 : ℝ) (r / 2),
          ∀ y ∈ Metric.closedBall (chartAt E x x) (r / 2),
            ‖iteratedFDeriv ℝ k
              (fun z : E ↦ chartAt E x (a t ((chartAt E x).symm z))) y‖ ≤ C) := by
    let e := chartAt E x
    have hx : x ∈ e.source := mem_chart_source E x
    have hy : e x ∈ e.target := e.map_source hx
    have h₀ : (0 : ℝ) +ᵥ e.symm (e x) ∈ e.source := by
      simpa only [zero_vadd, e.left_inv hx] using hx
    obtain ⟨r, hr, hdom⟩ :=
      VectorActionSpatialSupport.exists_action_coordinate_product e e 0 (e x) hy h₀
    have hjet (k : ℕ) := vector_action_spatial_derivatives_continuous hsmooth e e
        (IsManifold.chart_mem_maximalAtlas x) (IsManifold.chart_mem_maximalAtlas x)
        k _ (Metric.isOpen_ball.prod Metric.isOpen_ball)
        (fun p hp ↦ hdom p.1 hp.1 p.2 hp.2)
    refine ⟨r, hr, hdom, hjet, ?_, ?_⟩
    · intro y hy
      have hey : y ∈ e.target := (hdom 0 (Metric.mem_ball_self hr) y hy).1
      apply (hasFDerivAt_id y).congr_of_eventuallyEq
      filter_upwards [e.open_target.mem_nhds hey] with z hz
      simp only [hzero, id_eq]
      exact e.right_inv hz
    · intro k
      have hsmall : r / 2 < r := half_lt_self hr
      have hsub : Metric.closedBall (0 : ℝ) (r / 2) ×ˢ
          Metric.closedBall (e x) (r / 2) ⊆
          Metric.ball (0 : ℝ) r ×ˢ Metric.ball (e x) r := by
        intro p hp
        exact ⟨lt_of_le_of_lt hp.1 hsmall, lt_of_le_of_lt hp.2 hsmall⟩
      obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : ℝ) (r / 2)).prod
        (isCompact_closedBall (e x) (r / 2))).exists_bound_of_continuousOn
          ((hjet k).mono hsub)
      exact ⟨C, fun t ht y hy ↦ hC (t, y) ⟨ht, hy⟩⟩
  
  
  have haverage (x : M) : ∃ r > 0, ∀ h : ℝ, 0 ≤ h → h ≤ r / 2 →
      ∀ y ∈ Metric.ball (chartAt E x x) (r / 2), ∀ k : ℕ,
        HasFDerivAt
          (fun z ↦ ∫ t in 0..h, iteratedFDeriv ℝ k
            (fun w : E ↦ chartAt E x (a t ((chartAt E x).symm w))) z)
          (∫ t in 0..h, fderiv ℝ (iteratedFDeriv ℝ k
            (fun w : E ↦ chartAt E x (a t ((chartAt E x).symm w)))) y) y := by
    obtain ⟨r, hr, hdom, hjet, hzeroDeriv, hbound⟩ := hlocal x
    refine ⟨r, hr, ?_⟩
    intro h hh hh' y hy k
    let e := chartAt E x
    let f := fun t : ℝ ↦ fun w : E ↦ e (a t (e.symm w))
    have hsub : Set.uIcc 0 h ×ˢ Metric.closedBall (e x) (r / 2) ⊆
        Metric.ball (0 : ℝ) r ×ˢ Metric.ball (e x) r := by
      intro p hp
      have ht : 0 ≤ p.1 ∧ p.1 ≤ h := by
        simpa only [Set.uIcc_of_le hh, Set.mem_Icc] using hp.1
      refine ⟨?_, lt_of_le_of_lt hp.2 (half_lt_self hr)⟩
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      exact lt_of_le_of_lt (ht.2.trans hh') (half_lt_self hr)
    apply hasFDerivAt_intervalIntegral_of_compact_parameter
      (f := fun t ↦ iteratedFDeriv ℝ k (f t))
      (f' := fun t ↦ fderiv ℝ (iteratedFDeriv ℝ k (f t)))
      (isCompact_closedBall (e x) (r / 2))
      (Metric.closedBall_mem_nhds_of_mem hy)
    · exact (hjet k).mono hsub
    · exact (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (k + 1) ↦ E) E).continuous.comp_continuousOn
          ((hjet (k + 1)).mono hsub)
    · intro t ht z hz
      obtain ⟨ht', hz'⟩ := hsub (show (t, z) ∈ Set.uIcc 0 h ×ˢ Metric.closedBall (e x) (r / 2) from ⟨ht, hz⟩)
      obtain ⟨hztarget, hzsource⟩ := hdom t ht' z hz'
      exact (VectorActionSpatialSupport.action_coordinate_contDiffAt hsmooth e e
        (IsManifold.chart_mem_maximalAtlas x) (IsManifold.chart_mem_maximalAtlas x)
        t z hztarget hzsource).differentiableAt_iteratedFDeriv (m := k) (by exact_mod_cast (WithTop.coe_lt_top (a := k)))
          |>.hasFDerivAt
  exact one_parameter_smooth_generator_local_assembly a hcont hzero hadd hdiff haverage

end HolomorphicAnosov
