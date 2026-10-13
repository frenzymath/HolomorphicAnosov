import HolomorphicAnosov.Ghys.AffineCompletenessGlobalizeSurjectiveImageDiscSlopeData


noncomputable section
open Set Filter Topology _root_.Topology
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace

structure AffineCompletenessSurjectiveCertificate
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
    (D₀ : L i → ℂ) where
  image_radius : ℝ
  image_radius_pos : 0 < image_radius
  slope : ℕ → ℂ
  slope_ne_zero : ∀ n, slope n ≠ 0
  slope_unbounded : ∀ R : ℝ, ∃ n, R < ‖slope n‖
  image_disc_transport : ∀ n, Metric.ball (0 : ℂ) (image_radius * ‖slope n‖) ⊆ Set.range D₀
  surjective : Function.Surjective D₀


theorem affine_completeness_globalize_surjective_certificate
    {d : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    {ι : Type u} (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
    (G : NativeInvariantJetAffineLeafFamily f a L U) (i : ι)
    (D₀ : L i → ℂ)
    (hD₀ : ∀ c ∈ (G.affineAtlas i).charts, ∀ x ∈ c.source,
      ∃ b : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x,
        D₀ y = b.apply (c y)) :
    Nonempty (AffineCompletenessSurjectiveCertificate f a L U G i D₀) := by
  obtain ⟨h⟩ := affine_completeness_globalize_surjective_image_disc_slope_data
    f a L U G i D₀ hD₀
  refine ⟨{
    image_radius := h.image_radius
    image_radius_pos := h.image_radius_pos
    slope := h.slope
    slope_ne_zero := h.slope_ne_zero
    slope_unbounded := h.slope_unbounded
    image_disc_transport := h.image_disc_transport
    surjective := ?_
  }⟩
  intro z
  obtain ⟨n, hn⟩ := h.slope_unbounded (‖z‖ / h.image_radius)
  have hz : ‖z‖ < h.image_radius * ‖h.slope n‖ := by
    have := (div_lt_iff₀ h.image_radius_pos).mp hn
    simpa [mul_comm] using this
  exact h.image_disc_transport n (by simpa [Metric.mem_ball, dist_zero_right] using hz)


end HolomorphicAnosov.Ghys
