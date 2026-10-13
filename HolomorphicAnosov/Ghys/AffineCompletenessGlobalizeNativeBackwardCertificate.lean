import HolomorphicAnosov.Ghys.AffineCompletenessGlobalizeNativeBackwardData



noncomputable section
open Set Filter Topology _root_.Topology
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace

structure AffineCompletenessNativeBackwardCertificate
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
  injective : Function.Injective D₀


theorem affine_completeness_globalize_native_backward_certificate
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
    Nonempty (AffineCompletenessNativeBackwardCertificate f a L U G i D₀ hD₀) := by
  obtain ⟨h⟩ := affine_completeness_globalize_native_backward_data f a L U G i D₀ hD₀
  let : MetricSpace (L i) := h.sourceMetric
  let : ∀ n, MetricSpace (h.carrier n) := h.metric
  obtain ⟨C, ρ, hρ, hρ1, hcontract⟩ := h.contraction
  have hinj : Function.Injective D₀ :=
    affine_completeness_injective_of_backward_contraction D₀ h.development h.backward
      h.slope h.translation hρ hρ1 h.separation_radius_pos h.backward_injective
      hcontract h.slope_ne_zero h.transport h.separation
  exact ⟨{
    carrier := h.carrier
    sourceMetric := h.sourceMetric
    metric := h.metric
    development := h.development
    backward := h.backward
    slope := h.slope
    translation := h.translation
    slope_ne_zero := h.slope_ne_zero
    contraction := ⟨C, ρ, hρ, hρ1, hcontract⟩
    transport := h.transport
    separation_radius := h.separation_radius
    separation_radius_pos := h.separation_radius_pos
    separation := h.separation
    injective := hinj
  }⟩

end HolomorphicAnosov.Ghys
