import HolomorphicAnosov.Geometry.Manifold.VectorActionSpatialDerivativesContinuous
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Slope

open scoped Topology _root_.Topology Interval
open MeasureTheory Filter
/-! Short-time invertibility of averaged Jacobians for smooth actions. -/

namespace HolomorphicAnosov

/-- A Jacobian continuous at the identity has an invertible normalized time average for some arbitrarily small positive time. (Bochner–Montgomery, Lemma 2.) -/
theorem normalized_average_integral_invertible_g1
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (J : ℝ → E →L[ℝ] E)
    (hcont : ContinuousAt J 0)
    (hmeas : StronglyMeasurableAtFilter J (𝓝 0))
    (hzero : J 0 = ContinuousLinearMap.id ℝ E)
    (r : ℝ) (hr : 0 < r) :
    ∃ h : ℝ, 0 < h ∧ h < r ∧
      (h⁻¹ • ∫ t in 0..h, J t).IsInvertible := by
  have hd : HasDerivAt (fun h : ℝ ↦ ∫ t in 0..h, J t) (J 0) 0 :=
    intervalIntegral.integral_hasDerivAt_right (IntervalIntegrable.refl) hmeas hcont
  have ht : Tendsto (fun h : ℝ ↦ h⁻¹ • ∫ t in 0..h, J t)
      (𝓝[>] 0) (𝓝 (ContinuousLinearMap.id ℝ E)) := by
    simpa only [zero_add, intervalIntegral.integral_same, sub_zero, hzero]
      using hd.tendsto_slope_zero_right
  have hId : (ContinuousLinearMap.id ℝ E).IsInvertible := by
    simpa only [ContinuousLinearEquiv.coe_refl] using
      (ContinuousLinearMap.isInvertible_equiv (f := ContinuousLinearEquiv.refl ℝ E))
  have hi := ht.eventually hId.eventually_nhds
  have hp : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
  have hb : ∀ᶠ h : ℝ in 𝓝[>] 0, h < r :=
    (eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds
  obtain ⟨h, hh, hh', hh''⟩ := (hp.and (hb.and hi)).exists
  exact ⟨h, hh, hh', hh''⟩

/-- Removing the nonzero positive normalizing scalar preserves invertibility. -/
theorem average_integral_invertible_g1
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (J : ℝ → E →L[ℝ] E)
    (hcont : ContinuousAt J 0)
    (hmeas : StronglyMeasurableAtFilter J (𝓝 0))
    (hzero : J 0 = ContinuousLinearMap.id ℝ E)
    (r : ℝ) (hr : 0 < r) :
    ∃ h : ℝ, 0 < h ∧ h < r ∧
      (∫ t in 0..h, J t).IsInvertible := by
  obtain ⟨h, hp, hb, A, hA⟩ := normalized_average_integral_invertible_g1 J hcont hmeas hzero r hr
  refine ⟨h, hp, hb, (Units.mk0 h hp.ne') • A, ?_⟩
  have hscale : (((Units.mk0 h hp.ne') • A : E ≃L[ℝ] E) : E →L[ℝ] E) =
      h • (A : E →L[ℝ] E) := by ext x; rfl
  rw [hscale, hA, smul_smul, mul_inv_cancel₀ hp.ne', one_smul]

open scoped Manifold ContDiff
open Set
/-- An arbitrarily short positive time gives an invertible averaged spatial Jacobian at the center of the native chart for a continuous smooth-slice action. (Bochner–Montgomery, Lemma 2.) -/
theorem action_chart_average_invertible_g1
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (a : ℝ → M → M) (hcont : Continuous (Function.uncurry a))
    (hzero : ∀ x, a 0 x = x)
    (hadd : ∀ s t x, a s (a t x) = a (s + t) x)
    (hdiff : ∀ t, ∃ g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ x, g x = a t x)
    (x : M) (R : ℝ) (hR : 0 < R) :
    ∃ h : ℝ, 0 < h ∧ h < R ∧
      (∫ t in 0..h, fderiv ℝ
        (fun y : E ↦ chartAt E x (a t ((chartAt E x).symm y))) (chartAt E x x)).IsInvertible := by
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
  let e := chartAt E x
  have hx : x ∈ e.source := mem_chart_source E x
  have hy : e x ∈ e.target := e.map_source hx
  have h₀ : (0 : ℝ) +ᵥ e.symm (e x) ∈ e.source := by
    simpa only [zero_vadd, e.left_inv hx] using hx
  obtain ⟨r, hr, hdom⟩ :=
    VectorActionSpatialSupport.exists_action_coordinate_product e e 0 (e x) hy h₀
  let W : Set ℝ := Metric.ball 0 r
  let B : Set E := Metric.ball (e x) r
  let b := Module.finBasis ℝ E
  have hW : IsOpen W := Metric.isOpen_ball
  have hBmem : e x ∈ B := Metric.mem_ball_self hr
  obtain ⟨hF, hD, hH⟩ :=
    VectorActionSpatialSupport.action_coordinate_scalar_family_data
      hsmooth e e (IsManifold.chart_mem_maximalAtlas x)
      (IsManifold.chart_mem_maximalAtlas x) b W B hdom
  have hgood : Dense {v : W | ContinuousAt
      (fun q : ℝ × E ↦ fderiv ℝ (fun z ↦ e (q.1 +ᵥ e.symm z)) q.2)
        (v.val, e x)} := by
    apply VectorActionSpatialSupport.dense_good_parameters_of_coordinate_entries
      b W hW B Metric.isOpen_ball (e x) hBmem
    intro i j
    exact Analysis.Regularity.montgomery_directional_derivative_dense_joint_continuity
      W hW (e x) r (b j)
      (fun q ↦ b.equivFunL (e (q.1 +ᵥ e.symm q.2)) i)
      (fun q ↦ b.equivFunL (fderiv ℝ (fun z ↦ e (q.1 +ᵥ e.symm z)) q.2 (b j)) i)
      (hF i) (fun v hv z hz ↦ hD v hv z hz i j)
      (fun v hv ↦ hH v hv i j) (e x) hBmem
  let : Nonempty W := ⟨⟨0, Metric.mem_ball_self hr⟩⟩
  obtain ⟨v₀, hv₀⟩ := hgood.nonempty
  obtain ⟨hy₀, hv₀dom⟩ := hdom v₀.val v₀.property (e x) hBmem
  have hzeroC := VectorActionSpatialSupport.action_coordinate_good_parameter_to_identity
    hsmooth e e (IsManifold.chart_mem_maximalAtlas x)
    (IsManifold.chart_mem_maximalAtlas x) v₀.val (e x) hy₀ hv₀dom hv₀
  let J := fun t : ℝ ↦ fderiv ℝ (fun y : E ↦ e (a t (e.symm y))) (e x)
  have hJC : ContinuousOn J (Metric.ball 0 r) := by
    intro t ht
    have hct := VectorActionSpatialSupport.action_coordinate_identity_to_parameter
      hsmooth e e (IsManifold.chart_mem_maximalAtlas x)
      (IsManifold.chart_mem_maximalAtlas x) t (e x) hy (hdom t ht (e x) hBmem).2 hzeroC
    have hpair : ContinuousAt (fun s : ℝ ↦ (s, e x)) t :=
      continuousAt_id.prodMk continuousAt_const
    exact (hct.comp_of_eq hpair rfl).continuousWithinAt
  have hJ0 : J 0 = ContinuousLinearMap.id ℝ E := by
    have hid : HasFDerivAt (fun y : E ↦ e (a 0 (e.symm y)))
        (ContinuousLinearMap.id ℝ E) (e x) := by
      apply (hasFDerivAt_id (e x)).congr_of_eventuallyEq
      filter_upwards [e.open_target.mem_nhds hy] with y hy
      simp only [hzero, id_eq]
      exact e.right_inv hy
    exact hid.fderiv
  exact average_integral_invertible_g1 J
    (hJC.continuousAt (Metric.ball_mem_nhds _ hr))
    (hJC.stronglyMeasurableAtFilter Metric.isOpen_ball 0 (Metric.mem_ball_self hr)) hJ0 R hR
end HolomorphicAnosov


