import HolomorphicAnosov.Geometry.HermitianLeafPathDistance
import HolomorphicAnosov.Ghys.NativeInvariantJetAffineLeafFamily
import HolomorphicAnosov.Geometry.IntrinsicChartFirstExit
import HolomorphicAnosov.Ghys.AffineDevelopingConnectedChart
import HolomorphicAnosov.Ghys.NativeFlowboxMetricBounds

noncomputable section
open Set Filter Metric MeasureTheory _root_.Topology
open scoped ContDiff Manifold ENNReal
namespace HolomorphicAnosov.Ghys
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace
universe u v
variable {d : ℕ} {M : Type u} {L : Type v}
  [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
  [IsManifold (complexModel d) ∞ M]
  [TopologicalSpace L] [ChartedSpace (Fin 2 → ℝ) L]

/-- The literal given-g pullback speed on the original real leaf tangent fibre. (Ghys, p. 593) -/
def realMetricLeafSpeed
    (g : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : M ↦ TangentSpace (realModel d) x))
    (j : L → M) (x : L) (v : TangentSpace 𝓘(ℝ, Fin 2 → ℝ) x) : ℝ :=
  let w := mfderiv 𝓘(ℝ, Fin 2 → ℝ) (realModel d) j x v
  Real.sqrt (g.inner (j x) w w)

/-- Finite sum of the actual closed-piece speed integrals. (Ghys, p. 593) -/
def realMetricLeafPiecewiseLength
    (g : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : M ↦ TangentSpace (realModel d) x))
    (j : L → M) {x y : L} (p : IntrinsicPiecewiseC1Path (r := 2) x y) : ℝ≥0∞ :=
  ∑ i : Fin (p.n + 1), ∫⁻ t in p.pieceInterval i,
    ENNReal.ofReal (realMetricLeafSpeed g j (p.piece i t) (p.velocity i t))

/-- Infimum over paths in the same intrinsic leaf, measured in the given g. (Ghys, p. 593) -/
def intrinsicRealMetricLeafEDist
    (g : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : M ↦ TangentSpace (realModel d) x))
    (j : L → M) (x y : L) : ℝ≥0∞ :=
  ⨅ p : IntrinsicPiecewiseC1Path (r := 2) x y, realMetricLeafPiecewiseLength g j p

/-- The actual real operator norm of a development differential: supremum of standard complex output norms over the closed unit ball of the g-pullback input norm. (Ghys, p. 593) -/
def realMetricDevelopmentDerivativeNorm
    (g : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : M ↦ TangentSpace (realModel d) x))
    (j : L → M) (D : L → ℂ) (p : L) : ℝ :=
  sSup ((fun v : TangentSpace 𝓘(ℝ, Fin 2 → ℝ) p ↦
    ‖(tangentSpaceCastModel 𝓘(ℝ, ℂ) (D p))
      (mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) D p v)‖) ''
    {v | realMetricLeafSpeed g j p v ≤ 1})



/-- Quantitative scalar affine charts give intrinsic injectivity and a uniform image disk for centered developments with unit real metric derivative norm. (Ghys, p. 593) -/
theorem real_metric_affine_plaque_criterion
    {d : ℕ} {M N : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    [TopologicalSpace N] [T2Space N] [ChartedSpace (Fin 2 → ℝ) N]
    [IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ N]
    [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) ∞ N]
    (g : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : M ↦ TangentSpace (realModel d) x)) (j : N → M)
    (A : ComplexAffineAtlas N) (c : OpenPartialHomeomorph N ℂ)
    (hc : ContMDiffOn 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞ c c.source)
    (a : ℂ) (δ R m : ℝ) (hR : 0 < R) (hRδ : R < δ) (hm : 0 < m)
    (hbuffer : closedBall a δ ⊆ c.target)
    (hbound : ∀ x ∈ c.source, c x ∈ ball a δ → ∀ v : TangentSpace 𝓘(ℝ, Fin 2 → ℝ) x,
      m * ‖(tangentSpaceCastModel 𝓘(ℝ, ℂ) (c x))
        (mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) c x v)‖ ≤ realMetricLeafSpeed g j x v)
    (e : OpenPartialHomeomorph ℂ ℂ) (hes : e.source = ball a R)
    (hea : e a = 0) (he'a : deriv e a = 1)
    (he : ContDiffOn ℂ ∞ e e.source)
    (himage : ball 0 (R/2) ⊆ e.target)
    (hflat : c.trans e ∈ ComplexAffineStructure.maximalAtlas N
      (Quotient.mk (complexAffineAtlasSetoid N) A))
    {p : N} (hp : p ∈ c.source) (hpa : c p = a)
    (D : N → ℂ)
    (hD : ∀ c ∈ A.charts, ∀ x ∈ c.source,
      ∃ b : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, D y = b.apply (c y)) :
    (∀ y, intrinsicRealMetricLeafEDist g j p y < ENNReal.ofReal (m*R) → D p = D y → p = y) ∧
    (D p = 0 → realMetricDevelopmentDerivativeNorm g j D p = 1 →
      ball 0 (m*R/2) ⊆ range D) := by
  let cδ := c.trans (OpenPartialHomeomorph.ofSet (ball a δ) isOpen_ball)
  let q := c.trans e
  have hRtarget : ball a R ⊆ c.target :=
    (ball_subset_ball hRδ.le).trans (ball_subset_closedBall.trans hbuffer)
  have hδpos : 0 < δ := hR.trans hRδ
  have hqsource : q.source = c.symm '' ball a R := by
    ext x
    constructor
    · intro hx
      refine ⟨c x, ?_, c.left_inv hx.1⟩
      rw [← hes]
      exact hx.2
    · rintro ⟨z, hz, rfl⟩
      refine ⟨c.map_target (hRtarget hz), ?_⟩
      change c (c.symm z) ∈ e.source
      rw [c.right_inv (hRtarget hz), hes]
      exact hz
  have hqconn : IsPreconnected q.source := by
    rw [hqsource]
    exact (convex_ball a R).isPreconnected.image _ (c.symm.continuousOn.mono hRtarget)
  have hpq : p ∈ q.source := ⟨hp, by change c p ∈ e.source; rw [hpa, hes]; exact mem_ball_self hR⟩
  obtain ⟨b, hb⟩ := affine_developing_on_preconnected_chart A D hD q hflat hqconn hpq
  constructor
  · intro y hdist hDy
    have hcδ : ContMDiffOn 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) 1 cδ cδ.source :=
      (hc.of_le (by simp)).mono inter_subset_left
    have hbufδ : closedBall a R ⊆ cδ.target := by
      intro z hz
      exact ⟨(closedBall_subset_ball hRδ) hz, hbuffer ((closedBall_subset_closedBall hRδ.le) hz)⟩
    have hpδ : p ∈ cδ.source := ⟨hp, by change c p ∈ ball a δ; rw [hpa]; exact mem_ball_self hδpos⟩
    have hy := intrinsic_chart_ball_of_length_inf_lt cδ hcδ a R hR hbufδ
      (realMetricLeafSpeed g j) m hm (fun x hx v ↦ hbound x hx.1 hx.2 v) hpδ hpa hdist
    have hyq : y ∈ q.source := ⟨hy.1.1, by change c y ∈ e.source; rw [hes]; exact hy.2⟩
    apply q.injOn hpq hyq
    have h := (hb p hpq).symm.trans (hDy.trans (hb y hyq))
    exact mul_left_cancel₀ b.slope_ne_zero (add_right_cancel h)
  · intro hDp hnorm
    have hbp : b.translation = 0 := by
      have h := hb p hpq
      change D p = b.slope * e (c p) + b.translation at h
      simpa only [hpa, hea, mul_zero, zero_add, hDp] using h.symm
    have hderiv (v : TangentSpace 𝓘(ℝ, Fin 2 → ℝ) p) :
        (tangentSpaceCastModel 𝓘(ℝ, ℂ) (D p))
          (mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) D p v) =
        b.slope * (tangentSpaceCastModel 𝓘(ℝ, ℂ) (c p))
          (mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) c p v) := by
      apply real_chart_affine_unit_derivative b.slope b.translation
        ((hc.contMDiffAt (c.open_source.mem_nhds hp)).mdifferentiableAt (by simp))
      · have ha : a ∈ e.source := by rw [hes]; exact mem_ball_self hR
        rw [hpa]
        simpa only [he'a] using ((he.contDiffAt (e.open_source.mem_nhds ha)).differentiableAt (by simp)).hasDerivAt
      · filter_upwards [q.open_source.mem_nhds hpq] with x hx
        exact hb x hx
    have hcoef : m ≤ ‖b.slope‖ := by
      have hnonempty : ((fun v : TangentSpace 𝓘(ℝ, Fin 2 → ℝ) p ↦
        ‖(tangentSpaceCastModel 𝓘(ℝ, ℂ) (D p))
          (mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) D p v)‖) ''
        {v | realMetricLeafSpeed g j p v ≤ 1}).Nonempty := by
        apply Set.Nonempty.image
        exact ⟨0, by simp [realMetricLeafSpeed]⟩
      have hs : realMetricDevelopmentDerivativeNorm g j D p ≤ ‖b.slope‖ / m := by
        apply csSup_le hnonempty
        rintro z ⟨v, hv, rfl⟩
        dsimp only
        rw [hderiv, norm_mul]
        have hvb := hbound p hp (by rw [hpa]; exact mem_ball_self hδpos) v
        have hvc : ‖(tangentSpaceCastModel 𝓘(ℝ, ℂ) (c p))
            (mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) c p v)‖ ≤ 1/m := by
          apply (le_div_iff₀ hm).mpr
          change realMetricLeafSpeed g j p v ≤ 1 at hv
          nlinarith [hvb, hv]
        simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hvc (norm_nonneg b.slope)
      rw [hnorm] at hs
      simpa only [one_mul] using (le_div_iff₀ hm).mp hs
    intro y hy
    have hy' : y / b.slope ∈ ball (0 : ℂ) (R/2) := by
      rw [mem_ball, dist_zero_right, norm_div, div_lt_iff₀ (norm_pos_iff.mpr b.slope_ne_zero)]
      have hyn : ‖y‖ < m*R/2 := by simpa only [mem_ball, dist_zero_right] using hy
      nlinarith
    have hyt : y / b.slope ∈ q.target := by
      refine ⟨himage hy', ?_⟩
      exact hRtarget (by rw [← hes]; exact e.map_target (himage hy'))
    refine ⟨q.symm (y / b.slope), ?_⟩
    rw [hb _ (q.map_target hyt), q.right_inv hyt]
    simp only [ComplexAffineTransformation.apply, hbp, add_zero]
    field_simp [b.slope_ne_zero]

end HolomorphicAnosov.Ghys
