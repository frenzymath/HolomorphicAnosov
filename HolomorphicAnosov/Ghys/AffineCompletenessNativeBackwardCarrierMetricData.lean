import HolomorphicAnosov.Ghys.AffineCompletenessNativeBackwardMaps
import HolomorphicAnosov.Ghys.AffineCompletenessNativePullbackMetric
import HolomorphicAnosov.Ghys.AffineCompletenessLocalDevelopment


noncomputable section
open Set Filter Topology _root_.Topology
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace

structure AffineCompletenessNativeBackwardCarrierMetricData
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
  
  nativeCarrier : ∀ n, carrier n ≃ L ((G.permutation.symm : ι → ι)^[n] i)
  
  source_edist : ∀ x y, @edist (L i) sourceMetric.toEDist x y =
    intrinsicRealMetricLeafEDist a.metric (U.leaf i).inclusion x y
  
  receiving_edist : ∀ n x y, @edist (carrier n) (metric n).toEDist x y =
    intrinsicRealMetricLeafEDist a.metric
      (U.leaf ((G.permutation.symm : ι → ι)^[n] i)).inclusion
      (nativeCarrier n x) (nativeCarrier n y)
  
  native_backward : ∀ n, ∃ B : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
      (L i) (L ((G.permutation.symm : ι → ι)^[n] i)) ∞,
    (∀ x, nativeCarrier n (backward n x) = B x) ∧
    ∀ x, (U.leaf ((G.permutation.symm : ι → ι)^[n] i)).inclusion (B x) =
      ((f.symm : M → M)^[n]) ((U.leaf i).inclusion x)
  
  development_native : ∀ n (c : OpenPartialHomeomorph (L ((G.permutation.symm : ι → ι)^[n] i)) ℂ), c ∈ (G.affineAtlas
      ((G.permutation.symm : ι → ι)^[n] i)).charts → ∀ x, x ∈ c.source →
    ∃ b : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x,
      development n ((nativeCarrier n).symm y) = b.apply (c y)


theorem affine_completeness_native_backward_carrier_metric_data
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
    Nonempty (AffineCompletenessNativeBackwardCarrierMetricData f a L U G i D₀ hD₀) := by
  choose leafMetric htop hmetric using affine_completeness_native_pullback_metric f a L U
  choose D hD using affine_completeness_local_development f a L U G
  choose B hB using fun n => native_affine_backward_iterate f a L U G n i
  exact ⟨{
    carrier := fun n => L ((G.permutation.symm : ι → ι)^[n] i)
    sourceMetric := leafMetric i
    metric := fun n => leafMetric ((G.permutation.symm : ι → ι)^[n] i)
    development := fun n => D ((G.permutation.symm : ι → ι)^[n] i)
    backward := fun n => B n
    backward_injective := fun n => (B n).injective
    nativeCarrier := fun _ => Equiv.refl _
    source_edist := hmetric i
    receiving_edist := fun n => hmetric ((G.permutation.symm : ι → ι)^[n] i)
    native_backward := fun n => ⟨B n, fun _ => rfl, hB n⟩
    development_native := fun n c hc x hx => hD ((G.permutation.symm : ι → ι)^[n] i) c hc x hx
  }⟩

end HolomorphicAnosov.Ghys
