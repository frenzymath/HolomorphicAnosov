import HolomorphicAnosov.Geometry.Manifold.ZeroMFDerivConstancy
import HolomorphicAnosov.Paper.Ghys.SurfaceHolomorphicProductChartsBridge
import HolomorphicAnosov.Paper.Ghys.SurfaceProjectiveNativeOrderedAtlasBridge
import HolomorphicAnosov.Paper.Ghys.SurfaceProjectiveLocalProductChartBridge
import HolomorphicAnosov.Paper.Ghys.SurfaceOriginalChartInverse
import HolomorphicAnosov.Paper.Ghys.SurfaceProductTransitionFactors
import HolomorphicAnosov.Paper.Ghys.SurfaceGraphIntersectionContinuous
import HolomorphicAnosov.Paper.Ghys.SurfaceGraphIntersectionQuarterLipschitz
import HolomorphicAnosov.Analysis.Complex.LeblInjectiveHolomorphicBiholomorphism
import HolomorphicAnosov.Analysis.SeparatelyHolomorphicSmooth
import HolomorphicAnosov.Dynamics.Anosov.GlobalLamination
import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.SmoothComplexBundleHermitianMetric
import HolomorphicAnosov.Ghys.AffineProjectiveStructure
import HolomorphicAnosov.Paper.Ghys.Proposition31
import HolomorphicAnosov.Paper.Ghys.Proposition41
import HolomorphicAnosov.Paper.Ghys.StableHolonomyHolomorphic
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Paper.Zhang.CompactAnosovHermitianOperatorBounds
import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveProductDevelopment
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne

/-!
# Ordered holomorphic product charts for a holomorphic Anosov surface

This file constructs ordered holomorphic product charts from the stable and unstable leaf data of a holomorphic Anosov surface, with projective transitions compatible with the complete affine leaf structures (Ghys, Propositions 2.2, 3.1 and 4.1).
-/

noncomputable section

namespace HolomorphicAnosov.Ghys

open Set _root_.Topology
open scoped ContDiff Manifold

universe u

attribute [local instance] complex_isManifold_real

/-- For a compact holomorphic Anosov surface with stable and unstable complex rank one, the original stable and unstable plaques admit biholomorphic local product charts, and the resulting ordered atlas has locally constant projective transitions compatible with the complete affine structures (Ghys, Propositions 2.2, 3.1 and 4.1). -/
theorem surface_projective_g3_holomorphic_product_charts
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsCompactComplexManifold 2 S]
    (f : Biholomorph 2 2 S S) (a : AnosovDatum f)
    (stable_rank : HasComplexRankOne a.splitting.stable.toDistribution)
    (unstable_rank : HasComplexRankOne a.splitting.unstable.toDistribution) :
    ∃ A : OrderedProjectiveProductAtlas.{u, u} f a,
      ∀ (x : S) (α β : ℂ → S) (rα rβ : ℝ),
        0 < rα → 0 < rβ → α 0 = x → β 0 = x →
        ContMDiffOn 𝓘(ℂ) (complexModel 2) ∞ α (Metric.ball 0 rα) →
        ContMDiffOn 𝓘(ℂ) (complexModel 2) ∞ β (Metric.ball 0 rβ) →
        IsEmbedding (fun z : ↥(Metric.ball (0 : ℂ) rα) ↦ α z) →
        IsEmbedding (fun z : ↥(Metric.ball (0 : ℂ) rβ) ↦ β z) →
        (∀ z ∈ Metric.ball (0 : ℂ) rα,
          LinearMap.range (mfderiv 𝓘(ℝ, ℂ) (realModel 2) α z).toLinearMap =
            a.splitting.stable.toDistribution (α z)) →
        (∀ z ∈ Metric.ball (0 : ℂ) rβ,
          LinearMap.range (mfderiv 𝓘(ℝ, ℂ) (realModel 2) β z).toLinearMap =
            a.splitting.unstable.toDistribution (β z)) →
        ∃ (rs ru : ℝ) (e : OpenPartialHomeomorph (ℂ × ℂ) S) (i : A.index),
          0 < rs ∧ rs ≤ rα ∧ 0 < ru ∧ ru ≤ rβ ∧
          e.source = Metric.ball (0 : ℂ) rs ×ˢ Metric.ball (0 : ℂ) ru ∧
          x ∈ e.target ∧
          ContMDiffOn 𝓘(ℂ, ℂ × ℂ) (complexModel 2) ∞ e e.source ∧
          ContMDiffOn (complexModel 2) 𝓘(ℂ, ℂ × ℂ) ∞ e.symm e.target ∧
          ∀ s ∈ Metric.ball (0 : ℂ) rs, ∀ w ∈ Metric.ball (0 : ℂ) ru,
            α s ∈ (A.chart i).source ∧ β w ∈ (A.chart i).source ∧
            e (s, w) ∈ (A.chart i).source ∧
            A.chart i (e (s, w)) = ((A.chart i (α s)).1, (A.chart i (β w)).2) ∧
            e (s, 0) = α s ∧ e (0, w) = β w ∧
            ∀ y ∈ (A.chart i).source,
              ((A.chart i y).1 = (A.chart i (α s)).1 ∧
                (A.chart i y).2 = (A.chart i (β w)).2) ↔ y = e (s, w)  := by
  obtain ⟨A⟩ := surface_projective_g3_native_ordered_atlas_bridge_g7
    f a stable_rank unstable_rank
  exact ⟨A, surface_projective_g3_local_product_chart_bridge_g7
    f a stable_rank unstable_rank A⟩
end HolomorphicAnosov.Ghys
