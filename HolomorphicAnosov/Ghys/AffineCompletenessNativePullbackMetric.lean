import HolomorphicAnosov.Ghys.AffineCompletenessNativePullbackEDistFinite
import HolomorphicAnosov.Geometry.ImmersionRiemannianMetric
import HolomorphicAnosov.Geometry.IntrinsicPiecewiseC1RiemannianEDist
import Mathlib.Geometry.Manifold.Riemannian.Basic

noncomputable section
open Set Filter _root_.Topology TopologicalSpace
open scoped Manifold ContDiff ENNReal Bundle

namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace

variable {d : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
  (f : Biholomorph d d M M) (a : AnosovDatum f)
  {ι : Type u} (L : ι → Type u)
  [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
  [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
  [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
  (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))



omit [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)] in
theorem affine_completeness_native_pullback_metric (i : ι) :
    ∃ m : MetricSpace (L i),
      m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace (L i)) ∧
      ∀ x y : L i, @edist (L i) m.toEDist x y =
        intrinsicRealMetricLeafEDist a.metric (U.leaf i).inclusion x y := by
  obtain ⟨gL, hgL⟩ := immersion_riemannianMetric_exists a.metric
    (U.leaf i).inclusion (U.leaf i).immersion.contMDiff
    ((U.leaf i).immersion.mfderiv_injective (by simp))
  let : Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, Fin 2 → ℝ) : L i → Type _) :=
    ⟨gL.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (Fin 2 → ℝ)
      (TangentSpace 𝓘(ℝ, Fin 2 → ℝ) : L i → Type _) :=
    ⟨gL.inner, gL.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  let : T2Space (L i) := (U.leaf i).hausdorff
  let : LocallyCompactSpace (L i) := ChartedSpace.locallyCompactSpace (Fin 2 → ℝ) (L i)
  let m₁ : EMetricSpace (L i) := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, Fin 2 → ℝ) (L i)
  have heq (x y : L i) : @edist (L i) m₁.toEDist x y =
      intrinsicRealMetricLeafEDist a.metric (U.leaf i).inclusion x y := by
    change Manifold.riemannianEDist 𝓘(ℝ, Fin 2 → ℝ) x y = _
    rw [intrinsicPiecewiseC1Path_riemannianEDist]
    unfold intrinsicRealMetricLeafEDist realMetricLeafPiecewiseLength
    congr 1
    funext p
    apply Finset.sum_congr rfl
    intro k hk
    apply MeasureTheory.setLIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only
    rw [← ofReal_norm (p.velocity k t), norm_eq_sqrt_real_inner]
    change ENNReal.ofReal (Real.sqrt (gL.inner _ _ _)) = _
    rw [hgL]
    rfl
  have hfinite (x y : L i) : @edist (L i) m₁.toEDist x y ≠ ⊤ := by
    rw [heq]
    exact (affine_completeness_native_pullback_edist_lt_top f a L U i x y).ne
  exact ⟨@EMetricSpace.toMetricSpace (L i) m₁ hfinite, rfl, heq⟩

end HolomorphicAnosov.Ghys
