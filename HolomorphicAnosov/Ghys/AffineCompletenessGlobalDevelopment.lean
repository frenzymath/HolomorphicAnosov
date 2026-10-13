import HolomorphicAnosov.Ghys.AffineCompletenessLocalDevelopment
import HolomorphicAnosov.Ghys.AffineCompletenessIntrinsicSimplyConnected
import HolomorphicAnosov.Ghys.AffineCompletenessGlobalize
import HolomorphicAnosov.Ghys.NativeInvariantJetAffineLeafFamily

/-!
The invariant-section-induced affine atlas on each intrinsic unstable leaf admits a global
biholomorphic development onto `ℂ`. (Ghys, Lemma 3.3, p. 593) -/

noncomputable section
open Set Filter Topology _root_.Topology
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace

/-- Each intrinsic unstable leaf admits a biholomorphism onto `ℂ` whose germ in every chart of the
invariant-section-induced affine atlas is an invertible affine transformation. (Ghys, Lemma 3.3,
p. 593; Thurston, §3.5, pp. 34–35; Zhang, pp. 1, 4) -/
theorem affine_completeness_global_development
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
    (G : NativeInvariantJetAffineLeafFamily f a L U) (i : ι) :
    ∃ D : Diffeomorph (complexModel 1) 𝓘(ℂ) (L i) ℂ ∞,
      ∀ c ∈ (G.affineAtlas i).charts, ∀ x ∈ c.source,
        ∃ b : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, D y = b.apply (c y) := by
  let : ConnectedSpace (L i) := (U.leaf i).connected
  let : T2Space (L i) := (U.leaf i).hausdorff
  let : SecondCountableTopology (L i) := (U.leaf i).countable
  let : SimplyConnectedSpace (L i) :=
    affine_completeness_intrinsic_simply_connected_provider f a L U G i
  obtain ⟨D₀, hD₀⟩ := affine_completeness_local_development f a L U G i
  exact affine_completeness_globalize_development f a L U G i D₀ hD₀

end HolomorphicAnosov.Ghys
