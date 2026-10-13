import HolomorphicAnosov.Analysis.LogarithmicDifferentialClosed
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Scalar curvature under a gauge change and a pullback

Demailly, Complex Analytic and Differential Geometry (2012), V §3, p.256,
and Zhang §2.1 (5), p.5 and the curvature computation p.6. The scalar connection
pullback is a logarithmic gauge term plus the ordinary pullback of its one-form.
-/

noncomputable section
namespace HolomorphicAnosov

/-- The antisymmetrized derivative of `g⁻¹ dg + f* A` is `f* dA`.

Source: Demailly V §3 (3.1)–(3.4), p.256; Zhang §2.1 (5), p.5 and curvature p.6.
In real coordinates, differentiate the composition of `A ∘ f` with `Df`.
The chain rule contributes `DA(Df v)(Df w)`, and the derivative of `Df`
contributes `A(D²f(v,w))`. The latter cancels after antisymmetrization because
second derivatives are symmetric. The scalar gauge term has zero exterior
derivative by `scalar_gauge_curvature_invariant`. Only C² regularity of f and g
near the point and differentiability of A at its image are used. Neither
invertibility of f nor holomorphicity of the maps is required. -/
theorem scalar_gauge_pullback_curvature
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : F → F →L[ℝ] ℂ} {f : E → F} {g : E → ℂ} {x : E}
    (hA : DifferentiableAt ℝ A (f x)) (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) (hg0 : g x ≠ 0) (v w : E) :
    fderiv ℝ (fun y ↦ (g y)⁻¹ • fderiv ℝ g y + (A (f y)).comp (fderiv ℝ f y)) x v w -
      fderiv ℝ (fun y ↦ (g y)⁻¹ • fderiv ℝ g y + (A (f y)).comp (fderiv ℝ f y)) x w v =
        fderiv ℝ A (f x) (fderiv ℝ f x v) (fderiv ℝ f x w) -
          fderiv ℝ A (f x) (fderiv ℝ f x w) (fderiv ℝ f x v) := by
  have hdf : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hddf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hAf : DifferentiableAt ℝ (fun y ↦ A (f y)) x := hA.comp x hdf
  have hpull : DifferentiableAt ℝ (fun y ↦ (A (f y)).comp (fderiv ℝ f y)) x :=
    hAf.clm_comp hddf
  simp_rw [add_comm ((g _)⁻¹ • _) ((A (f _)).comp _)]
  rw [scalar_gauge_curvature_invariant hpull hg hg0]
  rw [fderiv_clm_comp hAf hddf, fderiv_fun_comp x hA hdf]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
  rw [hf.isSymmSndFDerivAt (by norm_num) v w]
  abel

end HolomorphicAnosov

