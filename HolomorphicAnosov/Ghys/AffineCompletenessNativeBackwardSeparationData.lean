import HolomorphicAnosov.Ghys.UniformIntrinsicNeighborhoods
import HolomorphicAnosov.Ghys.AffineCompletenessNativeBackwardCarrierMetricData


noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace

structure AffineCompletenessNativeBackwardSeparationData
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
  separation_radius : ℝ
  separation_radius_pos : 0 < separation_radius
  separation : ∀ n u v, @dist (carrier n) (metric n).toPseudoMetricSpace.toDist u v < separation_radius →
    development n u = development n v → u = v


theorem affine_completeness_native_backward_separation_data
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
    Nonempty (AffineCompletenessNativeBackwardSeparationData f a L U G i D₀ hD₀ hm.carrier hm.sourceMetric hm.metric hm.development hm.backward) := by
  obtain ⟨ε, r, hε, hr, hsep, himage⟩ :=
    affine_complete_uniform_intrinsic_neighborhoods L f a U G a.metric
  refine ⟨⟨ε, hε, ?_⟩⟩
  intro n u v huv hdev
  apply (hm.nativeCarrier n).injective
  apply hsep ((G.permutation.symm : ι → ι)^[n] i)
    (fun x ↦ hm.development n ((hm.nativeCarrier n).symm x))
    (hm.development_native n) (hm.nativeCarrier n u) (hm.nativeCarrier n v)
  · rw [← hm.receiving_edist n u v]
    let := hm.metric n
    rw [edist_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr huv
  · simpa only [Equiv.symm_apply_apply] using hdev

end HolomorphicAnosov.Ghys
