import HolomorphicAnosov.Ghys.NativeInvariantJetAffineLeafFamily



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



theorem native_affine_backward_map
    (G : NativeInvariantJetAffineLeafFamily f a L U) (i : ι) :
    ∃ B : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (L i) (L (G.permutation.symm i)) ∞,
      ∀ x, (U.leaf (G.permutation.symm i)).inclusion (B x) =
        f.symm ((U.leaf i).inclusion x) := by
  obtain ⟨j, rfl⟩ := G.permutation.surjective i
  rw [G.permutation.symm_apply_apply]
  refine ⟨(G.leafMap j).symm, ?_⟩
  intro x
  apply f.injective
  change f ((U.leaf j).inclusion ((G.leafMap j).symm x)) =
    f (f.symm ((U.leaf (G.permutation j)).inclusion x))
  rw [f.apply_symm_apply]
  simpa only [Diffeomorph.apply_symm_apply] using
    (G.leafMap_inclusion j ((G.leafMap j).symm x)).symm


theorem native_affine_backward_iterate
    (G : NativeInvariantJetAffineLeafFamily f a L U) (n : ℕ) (i : ι) :
    ∃ B : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (L i) (L ((G.permutation.symm : ι → ι)^[n] i)) ∞,
      ∀ x, (U.leaf ((G.permutation.symm : ι → ι)^[n] i)).inclusion (B x) =
        ((f.symm : M → M)^[n]) ((U.leaf i).inclusion x) := by
  induction n generalizing i with
  | zero =>
    exact ⟨Diffeomorph.refl 𝓘(ℂ) (L i) ∞, fun _ => rfl⟩
  | succ n ih =>
    obtain ⟨B₁, hB₁⟩ := native_affine_backward_map f a L U G i
    obtain ⟨Bₙ, hBₙ⟩ := ih (G.permutation.symm i)
    rw [Function.iterate_succ_apply (G.permutation.symm : ι → ι)]
    refine ⟨B₁.trans Bₙ, ?_⟩
    intro x
    change (U.leaf ((G.permutation.symm : ι → ι)^[n] (G.permutation.symm i))).inclusion
      (Bₙ (B₁ x)) = ((f.symm : M → M)^[n]) (f.symm ((U.leaf i).inclusion x))
    rw [hBₙ, hB₁]

end HolomorphicAnosov.Ghys
