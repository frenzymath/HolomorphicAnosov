import HolomorphicAnosov.Paper.Ghys.SurfaceHolomorphicProductChartsBridge
/-!
# Native ordered atlas existence bridge

This file records the bridge from the native HPS lamination and Ghys complete affine leaf structures to an ordered projective product atlas (Ghys, §§2–5; HPS, §§6B–7).
-/

noncomputable section
namespace HolomorphicAnosov.Ghys
open Set _root_.Topology
open scoped ContDiff Manifold
universe u
attribute [local instance] complex_isManifold_real

/-- The native stable and unstable leaf data of a compact holomorphic Anosov surface with complex rank one determine an ordered projective product atlas (Ghys, §§2–5; HPS, §§6B–7). -/
theorem surface_projective_g3_native_ordered_atlas_bridge_g7
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsCompactComplexManifold 2 S]
    (f : Biholomorph 2 2 S S) (a : AnosovDatum f)
    (stable_rank : HasComplexRankOne a.splitting.stable.toDistribution)
    (unstable_rank : HasComplexRankOne a.splitting.unstable.toDistribution) :
    Nonempty (OrderedProjectiveProductAtlas.{u, u} f a) := by
  let D := surface_projective_g3_holomorphic_product_charts_bridge_g7 f a stable_rank unstable_rank
  exact ⟨D.result.choose⟩

end HolomorphicAnosov.Ghys
