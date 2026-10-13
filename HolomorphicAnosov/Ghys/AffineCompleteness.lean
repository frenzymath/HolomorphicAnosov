import HolomorphicAnosov.Ghys.AffineCompletenessInjectivity
import HolomorphicAnosov.Ghys.AffineCompletenessGlobalDevelopment
import HolomorphicAnosov.Ghys.AffineProjectiveStructure
import HolomorphicAnosov.Paper.Ghys.InvariantJetSection
import HolomorphicAnosov.Ghys.NativeInvariantJetAffineLeafFamily
import HolomorphicAnosov.Ghys.AffineCompleteDevelopingContinuation
import HolomorphicAnosov.Ghys.UniformIntrinsicNeighborhoods
import HolomorphicAnosov.Ghys.JetAffineEquivalence
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.SmoothComplexBundleHermitianMetric
import Mathlib.Analysis.Convex.Contractible

/-!
The section-induced affine structures on intrinsic unstable leaves are complete, and their
developing maps are biholomorphisms onto `ℂ`, unique up to affine postcomposition. (Ghys, Lemma
3.3, p. 593) -/

noncomputable section
open Set Filter Topology _root_.Topology
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace

/-- Every intrinsic unstable leaf with its invariant-section-induced affine structure is complete
and admits a biholomorphic development onto `ℂ`. Every developing map is a biholomorphism, and
any two differ by an invertible affine postcomposition. (Ghys, Lemma 3.3, p. 593; Thurston,
§3.5, pp. 34–35; Zhang, p. 1) -/
theorem affine_completeness {d : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    {ι : Type u} (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
    (G : NativeInvariantJetAffineLeafFamily f a L U) :
    ∀ i : ι,
      let Develops := fun D : L i → ℂ ↦
        ∀ c ∈ (G.affineAtlas i).charts, ∀ x ∈ c.source,
          ∃ b : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, D y = b.apply (c y)
      (G.affineAt f a L U i).Complete (L i) ∧
      (∃ D : Diffeomorph (complexModel 1) 𝓘(ℂ) (L i) ℂ ∞,
        Develops (D : L i → ℂ)) ∧
      (∀ D : L i → ℂ, Develops D →
        ∃ e : Diffeomorph (complexModel 1) 𝓘(ℂ) (L i) ℂ ∞, ∀ x, e x = D x) ∧
      (∀ D₁ D₂ : L i → ℂ, Develops D₁ → Develops D₂ →
        ∃ b : ComplexAffineTransformation, ∀ x, D₂ x = b.apply (D₁ x)) := by
  intro i
  let : ConnectedSpace (L i) := (U.leaf i).connected
  obtain ⟨D, hD⟩ := affine_completeness_global_development f a L U G i
  
  let affineDiffeomorph (b : ComplexAffineTransformation) :
      Diffeomorph 𝓘(ℂ) 𝓘(ℂ) ℂ ℂ ∞ :=
    { toFun := b.apply
      invFun := fun z ↦ (z - b.translation) / b.slope
      left_inv := fun z ↦ by
        dsimp [ComplexAffineTransformation.apply]
        field_simp [b.slope_ne_zero]
        ring
      right_inv := fun z ↦ by
        dsimp [ComplexAffineTransformation.apply]
        field_simp [b.slope_ne_zero]
        ring
      contMDiff_toFun := (contMDiff_const.mul contMDiff_id).add contMDiff_const
      contMDiff_invFun := (contMDiff_id.sub contMDiff_const).div_const b.slope }
  let Q : ComplexAffineStructure (L i) := G.affineAt f a L U i
  have hQA : AffineAtlasesEquivalent (L i) Q.out (G.affineAtlas i) :=
    Quotient.exact (Quotient.out_eq Q)
  refine ⟨⟨?_, D, ?_⟩, ⟨D, hD⟩, ?_,
    affine_developing_uniqueness (L i) (G.affineAtlas i)⟩
  · exact D.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace
  · intro c hc x hxc
    obtain ⟨c', hc', hxc'⟩ := (G.affineAtlas i).cover x
    obtain ⟨b, hb⟩ := hQA c hc c' hc' x ⟨hxc, hxc'⟩
    obtain ⟨e, he⟩ := hD c' hc' x hxc'
    refine ⟨⟨e.slope * b.slope, mul_ne_zero e.slope_ne_zero b.slope_ne_zero,
      e.slope * b.translation + e.translation⟩, ?_⟩
    filter_upwards [hb, he] with y hby hey
    rw [hey, hby]
    dsimp [ComplexAffineTransformation.apply]
    ring
  · intro E hE
    obtain ⟨b, hb⟩ :=
      affine_developing_uniqueness (L i) (G.affineAtlas i) D E hD hE
    exact ⟨D.trans (affineDiffeomorph b), fun x ↦ (hb x).symm⟩

end HolomorphicAnosov.Ghys
