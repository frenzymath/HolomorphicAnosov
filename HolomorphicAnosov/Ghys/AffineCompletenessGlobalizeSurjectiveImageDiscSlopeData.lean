import HolomorphicAnosov.Ghys.AffineCompletenessNativeBackwardAffineTransportData
import HolomorphicAnosov.Ghys.UniformIntrinsicNeighborhoods
import HolomorphicAnosov.Ghys.RealMetricDevelopmentNormalizationG11
import HolomorphicAnosov.Ghys.NativeDevelopmentRealRegularityG11
import HolomorphicAnosov.Ghys.NativeBackwardDerivativeEstimatesG11
import Mathlib.Analysis.SpecificLimits.Basic



noncomputable section
open Set Filter Topology _root_.Topology
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace

structure AffineCompletenessSurjectiveImageDiscSlopeData
    {d : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    {ι : Type u} (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
    (G : NativeInvariantJetAffineLeafFamily f a L U) (i : ι)
    (D₀ : L i → ℂ) where
  image_radius : ℝ
  image_radius_pos : 0 < image_radius
  slope : ℕ → ℂ
  slope_ne_zero : ∀ n, slope n ≠ 0
  slope_unbounded : ∀ R : ℝ, ∃ n, R < ‖slope n‖
  image_disc_transport : ∀ n, Metric.ball (0 : ℂ) (image_radius * ‖slope n‖) ⊆ Set.range D₀


theorem affine_completeness_globalize_surjective_image_disc_slope_data
    {d : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    {ι : Type u} (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
    (G : NativeInvariantJetAffineLeafFamily f a L U) (i : ι)
    (D₀ : L i → ℂ)
    (hD₀ : ∀ c ∈ (G.affineAtlas i).charts, ∀ x ∈ c.source,
      ∃ b : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x,
        D₀ y = b.apply (c y)) :
    Nonempty (AffineCompletenessSurjectiveImageDiscSlopeData f a L U G i D₀) := by
  classical
  obtain ⟨hm⟩ := affine_completeness_native_backward_carrier_metric_data f a L U G i D₀ hD₀
  obtain ⟨ht⟩ := affine_completeness_native_backward_affine_transport_data f a L U G i D₀ hD₀ hm
  choose B hB hsq using hm.native_backward
  let j : ℕ → ι := fun n ↦ (G.permutation.symm : ι → ι)^[n] i
  let E : ∀ n, L (j n) → ℂ := fun n y ↦ D₀ ((B n).symm y)
  have hEeq (n : ℕ) (y : L (j n)) : E n y =
      ht.slope n * hm.development n ((hm.nativeCarrier n).symm y) + ht.translation n := by
    rw [show E n y = D₀ ((B n).symm y) from rfl, ht.transport]
    congr 2
    apply congrArg (hm.development n)
    apply (hm.nativeCarrier n).injective
    rw [hB, (B n).apply_symm_apply, (hm.nativeCarrier n).apply_symm_apply]
  have hEg (n : ℕ) : ∀ c ∈ (G.affineAtlas (j n)).charts, ∀ x ∈ c.source,
      ∃ b : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, E n y = b.apply (c y) := by
    intro c hc x hx
    obtain ⟨b, hb⟩ := hm.development_native n c hc x hx
    refine ⟨⟨ht.slope n * b.slope, mul_ne_zero (ht.slope_ne_zero n) b.slope_ne_zero,
      ht.slope n * b.translation + ht.translation n⟩, ?_⟩
    filter_upwards [hb] with y hy
    rw [hEeq, hy]
    simp only [ComplexAffineTransformation.apply]
    ring
  have hreg (n : ℕ) := native_development_real_regular (U.leaf (j n))
    (G.holomorphic_inclusion (j n)).1 (G.holomorphic_inclusion (j n)).2
    (G.affineAtlas (j n)) (E n) (hEg n)
  have hreg0 := native_development_real_regular (U.leaf i)
    (G.holomorphic_inclusion i).1 (G.holomorphic_inclusion i).2
    (G.affineAtlas i) D₀ hD₀
  let : ConnectedSpace (L i) := (U.leaf i).connected
  let x : L i := Classical.choice (inferInstance : Nonempty (L i))
  let p (n : ℕ) : L (j n) := B n x
  let N (n : ℕ) := realMetricDevelopmentDerivativeNorm a.metric
    (U.leaf (j n)).inclusion (E n) (p n)
  have hprops (n : ℕ) := real_metric_development_norm_properties a.metric
    (U.leaf (j n)).inclusion (E n) (p n)
    ((U.leaf (j n)).immersion.mfderiv_injective (by simp) _)
  have hNpos (n : ℕ) : 0 < N n := by
    apply (hprops n).2.2.1
    let : Nontrivial (TangentSpace 𝓘(ℝ, Fin 2 → ℝ) (p n)) :=
      inferInstanceAs (Nontrivial (Fin 2 → ℝ))
    intro hz
    apply LinearMap.ne_zero_of_injective ((hreg n).2 (p n))
    exact congrArg ContinuousLinearMap.toLinearMap hz
  obtain ⟨C, ρ, hC, hρ, hρ1, hspeed⟩ := native_backward_derivative_estimates f a L U
  let v : TangentSpace 𝓘(ℝ, Fin 2 → ℝ) x :=
    (tangentSpaceCastModel 𝓘(ℝ, Fin 2 → ℝ) x).symm (fun _ ↦ 1)
  have hv : v ≠ 0 := by
    intro hz
    have hh := congrArg (fun w ↦ (tangentSpaceCastModel 𝓘(ℝ, Fin 2 → ℝ) x) w 0) hz
    simp [v] at hh
  have hk : 0 < ‖mvfderiv 𝓘(ℝ, Fin 2 → ℝ) D₀ x v‖ := by
    apply norm_pos_iff.mpr
    intro hz
    apply hv
    exact (hreg0.2 x) (by simpa using hz)
  have hNu : ∀ R : ℝ, ∃ n, R < N n := by
    intro R
    by_contra! hR
    have hbound (n : ℕ) : ‖mvfderiv 𝓘(ℝ, Fin 2 → ℝ) D₀ x v‖ ≤
        R * (C * ρ ^ n * realMetricLeafSpeed a.metric (U.leaf i).inclusion x v) := by
      obtain ⟨hBr, hBn⟩ := hspeed n i (j n) (B n) (hsq n)
      have hd : mvfderiv 𝓘(ℝ, Fin 2 → ℝ) D₀ x v =
          mvfderiv 𝓘(ℝ, Fin 2 → ℝ) (E n) (p n)
            (mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) (B n) x v) := by
        have he : D₀ = E n ∘ B n := by funext y; simp [E]
        have hdiff := mfderiv_comp x ((hreg n).1.mdifferentiable (by simp) (p n))
          (hBr.mdifferentiable (by simp) x)
        have hh := congrArg (fun q : L i → ℂ ↦
          (mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) q x v : ℂ)) he
        change (mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) D₀ x v : ℂ) = _
        exact hh.trans (congrArg (fun q ↦ (q v : ℂ)) hdiff)
      rw [hd]
      apply ((hprops n).2.1 _).trans
      have hs := hBn x v
      have hnonneg : 0 ≤ realMetricLeafSpeed a.metric (U.leaf i).inclusion x v :=
        Real.sqrt_nonneg _
      exact (mul_le_mul_of_nonneg_left hs (hNpos n).le).trans
        (mul_le_mul_of_nonneg_right (hR n)
          (mul_nonneg (mul_nonneg hC.le (pow_nonneg hρ.le n)) hnonneg))
    have hlim : Tendsto (fun n : ℕ ↦ R * (C * ρ ^ n *
        realMetricLeafSpeed a.metric (U.leaf i).inclusion x v)) atTop (𝓝 0) := by
      simpa using (((tendsto_pow_atTop_nhds_zero_of_lt_one hρ.le hρ1).const_mul C).mul_const
        (realMetricLeafSpeed a.metric (U.leaf i).inclusion x v)).const_mul R
    exact (not_le_of_gt hk) (ge_of_tendsto' hlim hbound)
  obtain ⟨ε, r, hε, hr, _, hdisc⟩ := affine_complete_uniform_intrinsic_neighborhoods L f a U G a.metric
  have hexhaust (z : ℂ) : z ∈ range D₀ := by
    obtain ⟨n, hn⟩ := hNu (‖z - D₀ x‖ / r)
    let F : L (j n) → ℂ := fun y ↦ (N n)⁻¹ • (E n y - E n (p n))
    have hFg : ∀ c ∈ (G.affineAtlas (j n)).charts, ∀ w ∈ c.source,
        ∃ b : ComplexAffineTransformation, ∀ᶠ y in 𝓝 w, F y = b.apply (c y) := by
      intro c hc w hw
      obtain ⟨b, hb⟩ := hEg n c hc w hw
      refine ⟨⟨((N n)⁻¹ : ℝ) * b.slope, mul_ne_zero (by exact_mod_cast inv_ne_zero (hNpos n).ne')
        b.slope_ne_zero, ((N n)⁻¹ : ℝ) * (b.translation - E n (p n))⟩, ?_⟩
      filter_upwards [hb] with y hy
      simp only [F, hy, ComplexAffineTransformation.apply, Complex.real_smul]
      ring
    have hFn : realMetricDevelopmentDerivativeNorm a.metric (U.leaf (j n)).inclusion F (p n) = 1 :=
      real_metric_development_normalize a.metric (U.leaf (j n)).inclusion (E n) (p n)
        ((U.leaf (j n)).immersion.mfderiv_injective (by simp) _)
        ((hreg n).1.mdifferentiable (by simp) _) (hNpos n)
    have hball := hdisc (j n) (p n) F hFg (by simp [F]) hFn
    have hzball : (N n)⁻¹ • (z - D₀ x) ∈ Metric.ball (0 : ℂ) r := by
      simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_of_pos (hNpos n)]
      have hlt : ‖z - D₀ x‖ < r * N n := by simpa [mul_comm] using (div_lt_iff₀ hr).mp hn
      rw [inv_mul_eq_div, div_lt_iff₀ (hNpos n)]
      exact hlt
    obtain ⟨y, hy⟩ := hball hzball
    refine ⟨(B n).symm y, ?_⟩
    have hcenter : E n (p n) = D₀ x := by simp [E, p]
    change (N n)⁻¹ • (E n y - E n (p n)) = (N n)⁻¹ • (z - D₀ x) at hy
    rw [hcenter] at hy
    have hh : E n y - D₀ x = z - D₀ x := (smul_right_injective ℂ (inv_ne_zero (hNpos n).ne')) hy
    exact sub_left_inj.mp hh
  refine ⟨⟨1, zero_lt_one, fun n ↦ ((n : ℝ) + 1 : ℂ), ?_, ?_, ?_⟩⟩
  · intro n
    exact_mod_cast (by positivity : (n : ℝ) + 1 ≠ 0)
  · intro R
    obtain ⟨n, hn⟩ := exists_nat_gt R
    refine ⟨n, ?_⟩
    have he : ‖((n : ℝ) + 1 : ℂ)‖ = (n : ℝ) + 1 := by
      norm_cast
    rw [he]
    linarith
  · intro n z hz
    exact hexhaust z

end HolomorphicAnosov.Ghys
