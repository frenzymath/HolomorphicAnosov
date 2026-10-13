import HolomorphicAnosov.Ghys.NativeInvariantJetAffineLeafFamily
import HolomorphicAnosov.Analysis.HolomorphicSliceTwoDerivativesContinuous

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

/-- The first complex derivative of every scalar ambient coordinate of a native flowbox is jointly continuous on its genuine varying target domain. (Demailly, §3.B) -/
theorem native_flowbox_scalar_derivative_continuous
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
    (G : NativeInvariantJetAffineLeafFamily f a L U)
    (j : Fin G.boxCount) (ψ : OpenPartialHomeomorph M (ComplexModel d))
    (hψ : ψ ∈ IsManifold.maximalAtlas (complexModel d) ∞ M) (k : Fin d) :
    ContinuousOn
      (fun p : ℂ × (Fin (2*d-2) → ℝ) ↦
        deriv (fun z ↦ ψ ((G.box j).symm (z, p.2)) k) p.1)
      ((G.box j).target ∩ (G.box j).symm ⁻¹' ψ.source) := by
  have hopen : IsOpen ((G.box j).target ∩ (G.box j).symm ⁻¹' ψ.source) :=
    (G.box j).symm.continuousOn.isOpen_inter_preimage
      (G.box j).open_target ψ.open_source
  have hcont : ContinuousOn
      (fun p ↦ ψ ((G.box j).symm p) k)
      ((G.box j).target ∩ (G.box j).symm ⁻¹' ψ.source) := by
    apply (continuous_apply k).comp_continuousOn
    exact ψ.continuousOn.comp ((G.box j).symm.continuousOn.mono inter_subset_left)
      (fun _ hp ↦ hp.2)
  have hslice (t : G.transverse j) :
      ContMDiff 𝓘(ℂ) (complexModel d) ∞
        (fun z : nativeAffineFlowboxSlice (G.box j) t.val ↦
          (G.box j).symm (z.val, t.val)) := by
    have hp : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞
        (fun z : nativeAffineFlowboxSlice (G.box j) t.val ↦
          (G.parametrization j t z).val) :=
      contMDiff_subtype_val.comp (G.parametrization j t).contMDiff
    convert (G.holomorphic_inclusion (G.label j t)).1.comp hp using 1
    funext z
    exact G.parametrization_inclusion j t z
  have hambient (t : G.transverse j) :
      ContMDiffOn 𝓘(ℂ) (complexModel d) ∞
        (fun z : ℂ ↦ (G.box j).symm (z, t.val))
        {z | (z, t.val) ∈ (G.box j).target} := by
    intro z hz
    exact ((contMDiffAt_subtype_iff (I := 𝓘(ℂ)) (I' := complexModel d)
      (U := nativeAffineFlowboxSlice (G.box j) t.val)
      (f := fun z : ℂ ↦ (G.box j).symm (z, t.val))).mp
      ((hslice t).contMDiffAt
        (x := (⟨z, hz⟩ : nativeAffineFlowboxSlice (G.box j) t.val)))).contMDiffWithinAt
  have hdiff (t : Fin (2*d-2) → ℝ) :
      DifferentiableOn ℂ (fun z : ℂ ↦ ψ ((G.box j).symm (z, t)) k)
        {z | (z, t) ∈ (G.box j).target ∩ (G.box j).symm ⁻¹' ψ.source} := by
    by_cases ht : t ∈ G.transverse j
    · exact differentiableOn_pi.mp
        ((contMDiffOn_iff_contDiffOn.mp
          ((contMDiffOn_of_mem_maximalAtlas hψ).comp
            ((hambient ⟨t, ht⟩).mono (fun _ hz ↦ hz.1)) (fun _ hz ↦ hz.2))).differentiableOn
          (by simp)) k
    · intro z hz
      exact (ht (G.transverse_contains j (z, t) hz.1)).elim
  exact SliceDerivativePreparation.joint_deriv_continuousOn_open _ hopen _ hcont hdiff

end HolomorphicAnosov.Ghys

