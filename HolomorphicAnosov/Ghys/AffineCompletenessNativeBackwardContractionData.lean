import HolomorphicAnosov.Ghys.AffineCompletenessNativeBackwardCarrierMetricData
import Mathlib.Analysis.SpecificLimits.Basic
import HolomorphicAnosov.Geometry.IntrinsicRealMetricContraction
import HolomorphicAnosov.Paper.Zhang.FixedBlockUniformAnosovEstimates


noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff Bundle
namespace HolomorphicAnosov.Ghys
universe u


theorem identity_exponential_contraction_implies_subsingleton
    {X : Type*} [MetricSpace X] {C ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (h : ∀ (n : ℕ) (x y : X), dist x y ≤ C * ρ ^ n * dist x y) :
    Subsingleton X := by
  constructor
  intro x y
  have hdecay : Tendsto (fun n : ℕ ↦ C * ρ ^ n * dist x y) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ1).const_mul C).mul_const (dist x y)
  exact dist_le_zero.mp (ge_of_tendsto' hdecay (fun n ↦ h n x y))

attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace

structure AffineCompletenessNativeBackwardContractionData
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
      ∃ b : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, D₀ y = b.apply (c y))
    (carrier : ℕ → Type u) (sourceMetric : MetricSpace (L i))
    (metric : ∀ n, MetricSpace (carrier n))
    (backward : ∀ n, L i → carrier n) where
  C : ℝ
  ρ : ℝ
  rho_nonneg : 0 ≤ ρ
  rho_lt_one : ρ < 1
  contraction : ∀ n x y,
    @dist (carrier n) (metric n).toPseudoMetricSpace.toDist (backward n x) (backward n y) ≤
      C * ρ ^ n * @dist (L i) sourceMetric.toPseudoMetricSpace.toDist x y



theorem affine_completeness_native_backward_contraction_data
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
      ∃ b : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, D₀ y = b.apply (c y))
    (hm : AffineCompletenessNativeBackwardCarrierMetricData f a L U G i D₀ hD₀) :
    Nonempty (AffineCompletenessNativeBackwardContractionData f a L U G i D₀ hD₀
      hm.carrier hm.sourceMetric hm.metric hm.backward) := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.toRiemannianMetric⟩
  obtain ⟨C, ρ, hC, hρ, hρ1, _, hu⟩ := fixed_block_uniform_anosov_estimates f a
  refine ⟨⟨C, ρ, hρ.le, hρ1, ?_⟩⟩
  intro n x y
  obtain ⟨B, hB, hsq⟩ := hm.native_backward n
  let j := (G.permutation.symm : ι → ι)^[n] i
  have hinc (k : ι) : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) (realModel d) ∞
      (U.leaf k).inclusion := (U.leaf k).immersion.contMDiff
  have hBreal : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ B := by
    apply (ContMDiff.iff_comp_isImmersion (U.leaf j).immersion).2
    refine ⟨B.continuous, ?_⟩
    have heq : (U.leaf j).inclusion ∘ B =
        ((f.symm : M → M)^[n]) ∘ (U.leaf i).inclusion := funext hsq
    rw [heq]
    exact (f.toReal.symm.contMDiff.iterate n).comp (hinc i)
  have hF : ContMDiff (realModel d) (realModel d) ∞ ((f.symm : M → M)^[n]) :=
    f.toReal.symm.contMDiff.iterate n
  have hspeed : ∀ z (v : TangentSpace 𝓘(ℝ, Fin 2 → ℝ) z),
      realMetricLeafSpeed a.metric (U.leaf j).inclusion (B z)
        (mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) B z v) ≤
      (C * ρ ^ n) * realMetricLeafSpeed a.metric (U.leaf i).inclusion z v := by
    intro z v
    have heq : (U.leaf j).inclusion ∘ B =
        ((f.symm : M → M)^[n]) ∘ (U.leaf i).inclusion := funext hsq
    have hd : mfderiv 𝓘(ℝ, Fin 2 → ℝ) (realModel d) (U.leaf j).inclusion (B z)
        (mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) B z v) =
        mfderiv (realModel d) (realModel d) ((f.symm : M → M)^[n])
          ((U.leaf i).inclusion z)
          (mfderiv 𝓘(ℝ, Fin 2 → ℝ) (realModel d) (U.leaf i).inclusion z v) := by
      change @Eq (ComplexModel d) _ _
      have he := congrArg (fun q : L i → M ↦
        (mfderiv 𝓘(ℝ, Fin 2 → ℝ) (realModel d) q z v : ComplexModel d)) heq
      simpa only [mfderiv_comp z ((hinc j).mdifferentiable (by simp) _)
          (hBreal.mdifferentiable (by simp) _),
        mfderiv_comp z (hF.mdifferentiable (by simp) _)
          ((hinc i).mdifferentiable (by simp) _),
        ContinuousLinearMap.comp_apply] using he
    have hv : mfderiv 𝓘(ℝ, Fin 2 → ℝ) (realModel d) (U.leaf i).inclusion z v ∈
        a.splitting.unstable.toDistribution ((U.leaf i).inclusion z) := by
      rw [← (U.leaf i).tangent z]
      exact ⟨v, rfl⟩
    have hb := hu n ((U.leaf i).inclusion z) _ hv
    let H : M → ComplexModel d → ComplexModel d → ℝ := fun z v w ↦ a.metric.inner z v w
    change Real.sqrt (H ((U.leaf j).inclusion (B z)) _ _) ≤ _
    rw [hd, hsq z]
    have hnorm (q : M) (w : TangentSpace (realModel d) q) :
        ‖w‖ = Real.sqrt (a.metric.inner q w w) := rfl
    rw [hnorm, hnorm] at hb
    exact hb
  have he := intrinsicRealMetricLeafEDist_map_le a.metric B
    (hBreal.of_le (by simp)) (U.leaf i).inclusion (U.leaf j).inclusion
    (C * ρ ^ n) (mul_pos hC (pow_pos hρ n)) hspeed x y
  rw [← hB x, ← hB y, ← hm.receiving_edist, ← hm.source_edist] at he
  have ht := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (@edist_ne_top (L i) hm.sourceMetric.toPseudoMetricSpace x y)) he
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (mul_nonneg hC.le (pow_nonneg hρ.le n)), edist_dist, ENNReal.toReal_ofReal dist_nonneg] using ht

end HolomorphicAnosov.Ghys
