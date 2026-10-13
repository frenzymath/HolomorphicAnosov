import HolomorphicAnosov.Ghys.AffineCompletenessGlobalizeInjectivity
import HolomorphicAnosov.Ghys.CurveScalarIsManifoldComplex
import HolomorphicAnosov.Ghys.AffineDevelopingLocalDiffeomorph
import HolomorphicAnosov.Ghys.AffineCompletenessGlobalizeSurjectivity



noncomputable section
open Set Filter Topology _root_.Topology
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace


theorem affine_completeness_globalize_assemble
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
      ∃ b : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, D₀ y = b.apply (c y))
    (hInjective : Function.Injective D₀)
    (hSurjective : Function.Surjective D₀) :
    ∃ D : Diffeomorph (complexModel 1) 𝓘(ℂ) (L i) ℂ ∞,
      ∀ c ∈ (G.affineAtlas i).charts, ∀ x ∈ c.source,
        ∃ b : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, D y = b.apply (c y) := by
  let : IsManifold (complexModel 1) ∞ (L i) := curve_scalar_is_manifold_complex
  have hlocal := affine_developing_isLocalDiffeomorph
    (G.affineAtlas i) D₀ hD₀
  have hbij : Function.Bijective D₀ := ⟨hInjective, hSurjective⟩
  exact ⟨hlocal.diffeomorphOfBijective hbij, hD₀⟩

end HolomorphicAnosov.Ghys
