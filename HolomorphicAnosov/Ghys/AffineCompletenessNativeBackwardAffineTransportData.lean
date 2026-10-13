import HolomorphicAnosov.Ghys.AffineDevelopingUniqueness
import HolomorphicAnosov.Ghys.NativeAffineBackwardIterateDevelopment
import HolomorphicAnosov.Ghys.AffineCompletenessNativeBackwardCarrierMetricData


noncomputable section
open Set Filter _root_.Topology
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace

structure AffineCompletenessNativeBackwardAffineTransportData
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
    (carrier : ℕ → Type u) (development : ∀ n, carrier n → ℂ)
    (backward : ∀ n, L i → carrier n) where
  slope : ℕ → ℂ
  translation : ℕ → ℂ
  slope_ne_zero : ∀ n, slope n ≠ 0
  transport : ∀ n x, D₀ x = slope n * development n (backward n x) + translation n


theorem affine_completeness_native_backward_affine_transport_data
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
    Nonempty (AffineCompletenessNativeBackwardAffineTransportData f a L U G i D₀ hD₀
      hm.carrier hm.development hm.backward) := by
  classical
  have hex (n : ℕ) : ∃ b : ComplexAffineTransformation,
      ∀ x, D₀ x = b.apply (hm.development n (hm.backward n x)) := by
    obtain ⟨B, hB, hDB⟩ := native_affine_backward_iterate_development f a L U G n i D₀ hD₀
    let j := (G.permutation.symm : ι → ι)^[n] i
    let : ConnectedSpace (L j) := (U.leaf j).connected
    obtain ⟨b, hb⟩ := affine_developing_uniqueness (L j) (G.affineAtlas j)
      (fun y ↦ hm.development n ((hm.nativeCarrier n).symm y))
      (fun y ↦ D₀ (B.symm y)) (hm.development_native n) hDB
    refine ⟨b, ?_⟩
    intro x
    have hBx : hm.nativeCarrier n (hm.backward n x) = B x := by
      obtain ⟨B', hB', hambient⟩ := hm.native_backward n
      apply (U.leaf j).injective
      rw [hB', hambient, hB]
    have hx := hb (B x)
    rw [B.symm_apply_apply, ← hBx, (hm.nativeCarrier n).symm_apply_apply] at hx
    exact hx
  choose coeff hcoeff using hex
  exact ⟨{
    slope := fun n ↦ (coeff n).slope
    translation := fun n ↦ (coeff n).translation
    slope_ne_zero := fun n ↦ (coeff n).slope_ne_zero
    transport := hcoeff
  }⟩

end HolomorphicAnosov.Ghys
