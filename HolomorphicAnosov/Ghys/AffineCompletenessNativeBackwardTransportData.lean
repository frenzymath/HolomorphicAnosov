import HolomorphicAnosov.Ghys.AffineCompletenessNativeBackwardContractionData
import HolomorphicAnosov.Ghys.AffineCompletenessNativeBackwardAffineTransportData


noncomputable section
open Set Filter Topology _root_.Topology
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace

structure AffineCompletenessNativeBackwardTransportData
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
    (development : ∀ n, carrier n → ℂ) (backward : ∀ n, L i → carrier n) where
  slope : ℕ → ℂ
  translation : ℕ → ℂ
  slope_ne_zero : ∀ n, slope n ≠ 0
  contraction : ∃ C ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
    ∀ n x y, @dist (carrier n) (metric n).toPseudoMetricSpace.toDist (backward n x) (backward n y) ≤
      C * ρ ^ n * @dist (L i) sourceMetric.toPseudoMetricSpace.toDist x y
  transport : ∀ n x, D₀ x = slope n * development n (backward n x) + translation n


theorem affine_completeness_native_backward_transport_data
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
    Nonempty (AffineCompletenessNativeBackwardTransportData f a L U G i D₀ hD₀ hm.carrier hm.sourceMetric hm.metric hm.development hm.backward) := by
  obtain ⟨hc⟩ := affine_completeness_native_backward_contraction_data
    f a L U G i D₀ hD₀ hm
  obtain ⟨ht⟩ := affine_completeness_native_backward_affine_transport_data
    f a L U G i D₀ hD₀ hm
  exact ⟨{
    slope := ht.slope
    translation := ht.translation
    slope_ne_zero := ht.slope_ne_zero
    contraction := ⟨hc.C, hc.ρ, hc.rho_nonneg, hc.rho_lt_one, hc.contraction⟩
    transport := ht.transport
  }⟩

end HolomorphicAnosov.Ghys
