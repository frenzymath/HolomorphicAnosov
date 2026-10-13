import HolomorphicAnosov.Ghys.AffineCompletenessGlobalizeAssembly
import HolomorphicAnosov.Ghys.NativeInvariantJetAffineLeafFamily



noncomputable section
open Set Filter Topology _root_.Topology
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace


theorem affine_completeness_globalize_development
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
    [ConnectedSpace (L i)] [T2Space (L i)] [SecondCountableTopology (L i)]
    [SimplyConnectedSpace (L i)]
    (D₀ : L i → ℂ)
    (hD₀ : ∀ c ∈ (G.affineAtlas i).charts, ∀ x ∈ c.source,
      ∃ b : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, D₀ y = b.apply (c y)) :
    ∃ D : Diffeomorph (complexModel 1) 𝓘(ℂ) (L i) ℂ ∞,
      ∀ c ∈ (G.affineAtlas i).charts, ∀ x ∈ c.source,
        ∃ b : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, D y = b.apply (c y) := by
  have hInjective := affine_completeness_globalize_injective f a L U G i D₀ hD₀
  have hSurjective := affine_completeness_globalize_surjective f a L U G i D₀ hD₀
  exact affine_completeness_globalize_assemble f a L U G i D₀ hD₀ hInjective hSurjective

end HolomorphicAnosov.Ghys
