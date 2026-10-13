import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Analysis.Calculus.ContDiff.Operations

open Set
open scoped Manifold ContDiff

namespace HolomorphicAnosov

/-- Affine rescaling of a smooth path from `[0, 1]` to a nondegenerate interval preserves its
endpoints and Riemannian extended length. (Lee, p.275) -/
theorem smooth_path_affine_rescale
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    [∀ x : M, ENorm (TangentSpace I x)]
    [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)]
    {γ : ℝ → M} (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ (Icc 0 1))
    {a b : ℝ} (hab : a < b) :
    let η := fun t : ℝ ↦ γ ((t - a) / (b - a))
    ContMDiffOn 𝓘(ℝ) I ∞ η (Icc a b) ∧ η a = γ 0 ∧ η b = γ 1 ∧
      Manifold.pathELength I η a b = Manifold.pathELength I γ 0 1 := by
  have hba : 0 < b - a := sub_pos.mpr hab
  let f := fun t : ℝ ↦ (t - a) / (b - a)
  have hf : ContDiff ℝ ∞ f := (contDiff_id.sub contDiff_const).div_const _
  have hfa : f a = 0 := by simp [f]
  have hfb : f b = 1 := by simp [f, hba.ne']
  have hmono : Monotone f := fun x y hxy ↦
    div_le_div_of_nonneg_right (sub_le_sub_right hxy a) hba.le
  have hmem : MapsTo f (Icc a b) (Icc 0 1) := by
    intro t ht
    exact ⟨hfa ▸ hmono ht.1, hfb ▸ hmono ht.2⟩
  have hcomp := hγ.comp (contMDiff_iff_contDiff.mpr hf).contMDiffOn hmem
  refine ⟨hcomp, ?_, ?_, ?_⟩
  · change γ (f a) = γ 0
    rw [hfa]
  · change γ (f b) = γ 1
    rw [hfb]
  · have h := Manifold.pathELength_comp_of_monotoneOn (I := I) (γ := γ)
      hab.le (hmono.monotoneOn _) (hf.differentiable (by simp)).differentiableOn
      (by simpa only [hfa, hfb, Function.comp_def, f] using hγ.mdifferentiableOn (by simp))
    simpa only [hfa, hfb, Function.comp_def, f] using h

end HolomorphicAnosov

