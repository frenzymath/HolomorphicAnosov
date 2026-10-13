import HolomorphicAnosov.Ghys.AffineCompletenessInjectivity
import HolomorphicAnosov.Ghys.AffineCompletenessNativeBackwardCarrierData
import HolomorphicAnosov.Ghys.AffineCompletenessNativeBackwardTransportData
import HolomorphicAnosov.Ghys.NativeInvariantJetAffineLeafFamily



noncomputable section
open Set Filter Topology _root_.Topology
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace

structure AffineCompletenessNativeBackwardData
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
      ∃ b : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, D₀ y = b.apply (c y)) where
  carrier : ℕ → Type u
  sourceMetric : MetricSpace (L i)
  metric : ∀ n, MetricSpace (carrier n)
  development : ∀ n, carrier n → ℂ
  backward : ∀ n, L i → carrier n
  backward_injective : ∀ n, Function.Injective (backward n)
  slope : ℕ → ℂ
  translation : ℕ → ℂ
  slope_ne_zero : ∀ n, slope n ≠ 0
  contraction : ∃ C ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
    ∀ n x y, @dist (carrier n) (metric n).toPseudoMetricSpace.toDist (backward n x) (backward n y) ≤
      C * ρ ^ n * @dist (L i) sourceMetric.toPseudoMetricSpace.toDist x y
  transport : ∀ n x, D₀ x = slope n * development n (backward n x) + translation n
  separation_radius : ℝ
  separation_radius_pos : 0 < separation_radius
  separation : ∀ n u v, @dist (carrier n) (metric n).toPseudoMetricSpace.toDist u v < separation_radius →
    development n u = development n v → u = v


theorem affine_completeness_globalize_native_backward_data
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
    Nonempty (AffineCompletenessNativeBackwardData f a L U G i D₀ hD₀) := by
  obtain ⟨hc⟩ := affine_completeness_native_backward_carrier_data f a L U G i D₀ hD₀
  obtain ⟨ht⟩ := affine_completeness_native_backward_transport_data f a L U G i D₀ hD₀
    hc.toAffineCompletenessNativeBackwardCarrierMetricData
  exact ⟨{
    carrier := hc.carrier
    sourceMetric := hc.sourceMetric
    metric := hc.metric
    development := hc.development
    backward := hc.backward
    backward_injective := hc.backward_injective
    slope := ht.slope
    translation := ht.translation
    slope_ne_zero := ht.slope_ne_zero
    contraction := ht.contraction
    transport := ht.transport
    separation_radius := hc.separation_radius
    separation_radius_pos := hc.separation_radius_pos
    separation := hc.separation
  }⟩

end HolomorphicAnosov.Ghys
