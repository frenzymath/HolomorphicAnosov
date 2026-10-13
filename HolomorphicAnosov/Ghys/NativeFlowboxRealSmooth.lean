import HolomorphicAnosov.Ghys.NativeInvariantJetAffineLeafFamily

noncomputable section
open Set MeasureTheory Filter Topology _root_.Topology
open scoped ContDiff Manifold ENNReal

namespace HolomorphicAnosov.Ghys

universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace

variable {d : ℕ} {M : Type u} {ι : Type u} {L : ι → Type u}
  [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
  [IsManifold (complexModel d) ∞ M]
  [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
  [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
  [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]

/-- A native holomorphic plaque parametrization is smooth into the original real leaf atlas. (Ghys, Lemma 3.3) -/
theorem native_flowbox_parametrization_real_smooth
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
    (G : NativeInvariantJetAffineLeafFamily f a L U)
    (j : Fin G.boxCount) (t : G.transverse j) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 2 → ℝ) ∞
      (fun z : nativeAffineFlowboxSlice (G.box j) t.val ↦
        (G.parametrization j t z).val) := by
  have hp : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞
      (fun z : nativeAffineFlowboxSlice (G.box j) t.val ↦
        (G.parametrization j t z).val) :=
    contMDiff_subtype_val.comp (G.parametrization j t).contMDiff
  have hcomplex := (G.holomorphic_inclusion (G.label j t)).1.comp hp
  intro z
  apply (ContMDiffAt.iff_comp_isImmersionAt
    ((U.leaf (G.label j t)).immersion.isImmersionAt _)).mpr
  refine ⟨hp.continuous.continuousAt, ?_⟩
  obtain ⟨hc, hd⟩ := contMDiffAt_iff.mp (hcomplex z)
  exact contMDiffAt_iff.mpr ⟨hc, hd.restrict_scalars ℝ⟩

end HolomorphicAnosov.Ghys

