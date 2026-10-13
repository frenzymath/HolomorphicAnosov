import HolomorphicAnosov.Ghys.NativeInvariantJetGraphEquivG1

noncomputable section
open Set Filter _root_.Topology TopologicalSpace
open scoped Manifold ContDiff

namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace

variable {d : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
  (f : Biholomorph d d M M) (a : AnosovDatum f)
  {ι : Type u} (L : ι → Type u)
  [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
  [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
  [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
  (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))


/-- A development pulls forward along the inverse native dynamics and remains a development on the exact inverse-orbit leaf. Source: Ghys, Holomorphic Anosov systems, Lemmas 3. -/
theorem native_affine_backward_iterate_development
    (G : NativeInvariantJetAffineLeafFamily f a L U) (n : ℕ) (i : ι)
    (D : L i → ℂ)
    (hD : ∀ c ∈ (G.affineAtlas i).charts, ∀ x ∈ c.source,
      ∃ b : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, D y = b.apply (c y)) :
    ∃ B : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (L i) (L ((G.permutation.symm : ι → ι)^[n] i)) ∞,
      (∀ x, (U.leaf ((G.permutation.symm : ι → ι)^[n] i)).inclusion (B x) =
        ((f.symm : M → M)^[n]) ((U.leaf i).inclusion x)) ∧
      ∀ c ∈ (G.affineAtlas ((G.permutation.symm : ι → ι)^[n] i)).charts,
        ∀ x ∈ c.source, ∃ b : ComplexAffineTransformation,
          ∀ᶠ y in 𝓝 x, D (B.symm y) = b.apply (c y) := by
  have hforward (j : ι) (D : L (G.permutation j) → ℂ)
      (hD : ∀ e ∈ (G.affineAtlas (G.permutation j)).charts, ∀ x ∈ e.source,
        ∃ b : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, D y = b.apply (e y)) :
      ∀ c ∈ (G.affineAtlas j).charts, ∀ x ∈ c.source,
        ∃ b : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x,
          D (G.leafMap j y) = b.apply (c y) := by
    intro c hc x hx
    obtain ⟨e, he, hxe⟩ := (G.affineAtlas (G.permutation j)).cover (G.leafMap j x)
    have hemax : e ∈ ComplexAffineStructure.maximalAtlas _
        (G.affineAt f a L U (G.permutation j)) := by
      rw [NativeInvariantJetAffineLeafFamily.affineAt,
        ComplexAffineStructure.maximalAtlas_eq_of_representative]
      exact ⟨(G.affineAtlas _).holomorphic e he,
        fun c hc ↦ (G.affineAtlas _).compatible c hc e he⟩
    have hp := native_invariant_affine_chart_pullback_g1 f a L U G j e hemax
    rw [NativeInvariantJetAffineLeafFamily.affineAt,
      ComplexAffineStructure.maximalAtlas_eq_of_representative] at hp
    obtain ⟨b, hb⟩ := hp.2 c hc x ⟨hx, by simpa using hxe⟩
    obtain ⟨a₀, ha₀⟩ := hD e he (G.leafMap j x) hxe
    refine ⟨⟨a₀.slope * b.slope, mul_ne_zero a₀.slope_ne_zero b.slope_ne_zero,
      a₀.slope * b.translation + a₀.translation⟩, ?_⟩
    filter_upwards [(G.leafMap j).continuous.continuousAt.eventually ha₀, hb] with y hay hby
    change e (G.leafMap j y) = b.apply (c y) at hby
    rw [hay, hby]
    dsimp [ComplexAffineTransformation.apply]
    ring
  induction n generalizing i with
  | zero =>
      exact ⟨Diffeomorph.refl 𝓘(ℂ) (L i) ∞, fun _ ↦ rfl, hD⟩
  | succ n ih =>
      obtain ⟨j, rfl⟩ := G.permutation.surjective i
      rw [Function.iterate_succ_apply (G.permutation.symm : ι → ι),
        G.permutation.symm_apply_apply]
      obtain ⟨B, hB, hBD⟩ := ih j (fun y ↦ D (G.leafMap j y)) (hforward j D hD)
      refine ⟨(G.leafMap j).symm.trans B, ?_, ?_⟩
      · intro x
        change (U.leaf ((G.permutation.symm : ι → ι)^[n] j)).inclusion
          (B ((G.leafMap j).symm x)) = _
        rw [hB, Function.iterate_succ_apply]
        congr 1
        apply f.injective
        change f ((U.leaf j).inclusion ((G.leafMap j).symm x)) =
          f (f.symm ((U.leaf (G.permutation j)).inclusion x))
        rw [f.apply_symm_apply]
        simpa using (G.leafMap_inclusion j ((G.leafMap j).symm x)).symm
      · exact hBD

end HolomorphicAnosov.Ghys
