import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Tactic.NormNum

/-! This file proves tangency of Lie brackets to the range of a continuous linear map with a
continuous linear left inverse. (Lee, Prop. 4.16, p. 92; Cor. 8.28, p. 193) -/

noncomputable section
open Set Filter Function
open scoped Topology _root_.Topology ContDiff
namespace HolomorphicAnosov.Theorem12NativePlaque
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The Lie bracket of differentiable vector fields tangent along a split linear subspace lies in
that subspace. (Lee, Prop. 4.16, p. 92; Cor. 8.28, p. 193) -/
theorem lieBracket_mem_linear_range
    (A : E →L[ℝ] H) (B : H →L[ℝ] E) (hBA : ∀ u, B (A u) = u)
    {ξ : E}
    {V W : H → H} (hV : DifferentiableAt ℝ V (A ξ))
    (hW : DifferentiableAt ℝ W (A ξ))
    (hVtan : ∀ᶠ u in 𝓝 ξ, V (A u) ∈ A.range)
    (hWtan : ∀ᶠ u in 𝓝 ξ, W (A u) ∈ A.range) :
    VectorField.lieBracket ℝ V W (A ξ) ∈ A.range := by
  let v : E → E := fun u ↦ B (V (A u))
  let w : E → E := fun u ↦ B (W (A u))
  have hv : DifferentiableAt ℝ v ξ := B.differentiableAt.comp ξ
    (hV.comp ξ A.differentiableAt)
  have hw : DifferentiableAt ℝ w ξ := B.differentiableAt.comp ξ
    (hW.comp ξ A.differentiableAt)
  have hrelV : (fun u ↦ A (v u)) =ᶠ[𝓝 ξ] (fun u ↦ V (A u)) := by
    filter_upwards [hVtan] with u hu
    rcases hu with ⟨a, ha⟩
    dsimp [v]
    rw [← ha]
    change A (B (A a)) = A a
    rw [hBA]
  have hrelW : (fun u ↦ A (w u)) =ᶠ[𝓝 ξ] (fun u ↦ W (A u)) := by
    filter_upwards [hWtan] with u hu
    rcases hu with ⟨a, ha⟩
    dsimp [w]
    rw [← ha]
    change A (B (A a)) = A a
    rw [hBA]
  refine ⟨VectorField.lieBracket ℝ v w ξ, ?_⟩
  change A (VectorField.lieBracket ℝ v w ξ) = _
  have hA2 : ContDiffAt ℝ 2 A ξ := A.contDiff.contDiffAt
  have hid := VectorField.fderiv_apply_lieBracket hA2 (by norm_num) hw hv
  simp only [ContinuousLinearMap.fderiv] at hid
  rw [hid, hrelW.fderiv_eq, hrelV.fderiv_eq]
  change fderiv ℝ (W ∘ A) ξ (v ξ) - fderiv ℝ (V ∘ A) ξ (w ξ) = _
  rw [(hW.hasFDerivAt.comp ξ A.hasFDerivAt).fderiv,
    (hV.hasFDerivAt.comp ξ A.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.comp_apply, hrelV.self_of_nhds,
    hrelW.self_of_nhds, VectorField.lieBracket]

end HolomorphicAnosov.Theorem12NativePlaque

