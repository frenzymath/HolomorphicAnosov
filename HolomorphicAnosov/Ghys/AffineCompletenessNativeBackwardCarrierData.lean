import HolomorphicAnosov.Ghys.NativeInvariantJetAffineLeafFamily
import HolomorphicAnosov.Ghys.AffineCompletenessNativeBackwardCarrierMetricData
import HolomorphicAnosov.Ghys.AffineCompletenessNativeBackwardSeparationData


noncomputable section
open Set Filter Topology _root_.Topology
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace

structure AffineCompletenessNativeBackwardCarrierData
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
      ∃ b : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, D₀ y = b.apply (c y)) extends AffineCompletenessNativeBackwardCarrierMetricData f a L U G i D₀ hD₀ where
  separation_radius : ℝ
  separation_radius_pos : 0 < separation_radius
  separation : ∀ n u v, @dist (carrier n) (metric n).toPseudoMetricSpace.toDist u v < separation_radius →
    development n u = development n v → u = v


theorem affine_completeness_native_backward_carrier_data
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
      ∃ b : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, D₀ y = b.apply (c y)) :
    Nonempty (AffineCompletenessNativeBackwardCarrierData f a L U G i D₀ hD₀) := by
  obtain ⟨hm⟩ := affine_completeness_native_backward_carrier_metric_data f a L U G i D₀ hD₀
  obtain ⟨hs⟩ := affine_completeness_native_backward_separation_data f a L U G i D₀ hD₀
    hm
  exact ⟨{
    toAffineCompletenessNativeBackwardCarrierMetricData := hm
    separation_radius := hs.separation_radius
    separation_radius_pos := hs.separation_radius_pos
    separation := hs.separation
  }⟩

end HolomorphicAnosov.Ghys
