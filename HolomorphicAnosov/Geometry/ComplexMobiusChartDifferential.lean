import HolomorphicAnosov.Geometry.ComplexMobiusPSLNormalization
import HolomorphicAnosov.SurfaceTorusSupport.ProjectiveActionHolomorphic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

noncomputable section
open Set Filter Topology _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov
open Ghys

/-- In a ratio chart about its image, a complex Möbius transformation composed with the finite chart has surjective real differential. (Demailly, V §15.A, p. 277; Ghys, §5, p. 597). -/
theorem complex_mobius_chart_differential (g : ComplexMobiusTransformation)
    (z : ComplexModel 1) :
    ∃ k : Fin 2, g.apply (complexProjectiveLineChartInv 1 z) ∈
        complexProjectiveLineChartSource k ∧
      DifferentiableAt ℝ (fun w ↦ complexProjectiveLineChartFun k
        (g.apply (complexProjectiveLineChartInv 1 w))) z ∧
      Function.Surjective (fderiv ℝ (fun w ↦ complexProjectiveLineChartFun k
        (g.apply (complexProjectiveLineChartInv 1 w))) z) := by
  obtain ⟨a, ha, _⟩ := complex_mobius_psl_normalization g
  let action : ComplexProjectiveLine ≃ₜ ComplexProjectiveLine :=
    { toEquiv :=
        { toFun := fun p ↦ a • p
          invFun := fun p ↦ a⁻¹ • p
          left_inv := fun p ↦ by simp
          right_inv := fun p ↦ by simp }
      continuous_toFun := (projective_special_linear_action_contMDiff a).continuous
      continuous_invFun := (projective_special_linear_action_contMDiff a⁻¹).continuous }
  obtain ⟨k, hk⟩ : ∃ k : Fin 2, a • complexProjectiveLineChartInv 1 z ∈
      complexProjectiveLineChartSource k := by
    rcases complexProjectiveLineChart_cover (a • complexProjectiveLineChartInv 1 z) with h | h
    · exact ⟨1, h⟩
    · exact ⟨0, h⟩
  let e := ((complexProjectiveLineChart 1).symm.trans action.toOpenPartialHomeomorph).trans
    (complexProjectiveLineChart k)
  have haction : action.toOpenPartialHomeomorph.MDifferentiable
      (complexModel 1) (complexModel 1) := by
    constructor
    · exact (projective_special_linear_action_contMDiff a).mdifferentiable (by simp) |>.mdifferentiableOn
    · exact (projective_special_linear_action_contMDiff a⁻¹).mdifferentiable (by simp) |>.mdifferentiableOn
  have he : e.MDifferentiable (complexModel 1) (complexModel 1) :=
    ((mdifferentiable_of_mem_atlas (show complexProjectiveLineChart 1 ∈
      atlas (ComplexModel 1) ComplexProjectiveLine from ⟨1, rfl⟩)).symm.trans haction).trans
      (mdifferentiable_of_mem_atlas ⟨k, rfl⟩)
  have hz : z ∈ e.source := by
    change z ∈ univ ∩ (complexProjectiveLineChart 1).symm ⁻¹' univ ∩
      (fun w ↦ action ((complexProjectiveLineChart 1).symm w)) ⁻¹'
        (complexProjectiveLineChart k).source
    exact ⟨⟨mem_univ _, mem_univ _⟩, hk⟩
  have hdiff : DifferentiableAt ℂ e z :=
    (mdifferentiableAt_iff_differentiableAt).mp (he.mdifferentiableAt hz)
  have hdi : DifferentiableAt ℂ e.symm (e z) :=
    mdifferentiableAt_iff_differentiableAt.mp (he.mdifferentiableAt_symm (e.map_source hz))
  have hright : e ∘ e.symm =ᶠ[𝓝 (e z)] id := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hz)] with w hw
    exact e.right_inv hw
  have hcomp : (fderiv ℂ e z).comp (fderiv ℂ e.symm (e z)) =
      ContinuousLinearMap.id ℂ (ComplexModel 1) := by
    have hdiff' : DifferentiableAt ℂ e (e.symm (e z)) := by rwa [e.left_inv hz]
    calc
      _ = fderiv ℂ (e ∘ e.symm) (e z) := by
        simpa only [e.left_inv hz] using (fderiv_comp (e z) hdiff' hdi).symm
      _ = fderiv ℂ id (e z) := hright.fderiv_eq
      _ = _ := fderiv_id
  have hsurj : Function.Surjective (fderiv ℂ e z) := by
    intro w
    exact ⟨fderiv ℂ e.symm (e z) w, congrArg (fun L ↦ L w) hcomp⟩
  have hefun : (e : ComplexModel 1 → ComplexModel 1) =
      (fun w ↦ complexProjectiveLineChartFun k (g.apply (complexProjectiveLineChartInv 1 w))) := by
    funext w
    exact congrArg (complexProjectiveLineChartFun k) (ha _)
  refine ⟨k, (ha _ ▸ hk), ?_, ?_⟩
  · rw [← hefun]
    exact hdiff.restrictScalars ℝ
  · rw [← hefun, hdiff.fderiv_restrictScalars ℝ]
    exact hsurj

end HolomorphicAnosov
