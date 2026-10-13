import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection

open Bundle Set _root_.Topology TopologicalSpace
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real

noncomputable section
namespace HolomorphicAnosov
namespace ConnectionCalculus

universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
  [T2Space X] [SecondCountableTopology X] [CompactSpace X]

omit [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
  [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- Multiplication of a locally smooth coordinate form by a smooth weight whose closed support lies
in its domain yields a smooth form on the chart target. (Zhang, after (4)) -/
theorem supported_chart_smul_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (O V : Opens X) (ρ : X → ℂ) (hρsupport : tsupport ρ ⊆ O)
    (c : OpenPartialHomeomorph X (ComplexModel d))
    (B : ComplexModel d → E)
    (hρ : ContDiffOn ℝ ∞ (fun z ↦ ρ (c.symm z)) c.target)
    (hB : ContDiffOn ℝ ∞ B
      (c.target ∩ c.symm ⁻¹' ((V : Set X) ∩ (O : Set X))))
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] :
    ContDiffOn ℝ ∞ (fun z ↦ ρ (c.symm z) • B z)
      (c.target ∩ c.symm ⁻¹' (V : Set X)) := by
  apply (c.isOpen_inter_preimage_symm V.isOpen).contDiffOn_iff.mpr
  intro z hz
  by_cases hO : c.symm z ∈ O
  · have hseed : IsOpen
        (c.target ∩ c.symm ⁻¹' ((V : Set X) ∩ (O : Set X))) :=
      c.isOpen_inter_preimage_symm (V.isOpen.inter O.isOpen)
    exact ((hρ.mono inter_subset_left).smul hB).contDiffAt
      (hseed.mem_nhds ⟨hz.1, hz.2, hO⟩)
  · have hzero : ρ =ᶠ[nhds (c.symm z)] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp (fun ht ↦ hO (hρsupport ht))
    have hinv : ContinuousAt c.symm z := c.continuousOn_symm.continuousAt
      (c.open_target.mem_nhds hz.1)
    apply (show ContDiffAt ℝ ∞ (fun _ : ComplexModel d ↦ (0 : E)) z from
      contDiffAt_const).congr_of_eventuallyEq
    filter_upwards [hinv.tendsto.eventually hzero] with y hy
    simp only [Pi.zero_apply] at hy
    simp [hy]



end ConnectionCalculus
end HolomorphicAnosov
