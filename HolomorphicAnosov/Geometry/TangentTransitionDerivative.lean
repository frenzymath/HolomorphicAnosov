import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! Derivatives of tangent-coordinate transitions and covariance of quadratic spray vectors.
(Andrews, Lecture 8, Exercises 8.3.2 and 8.11.3) -/

namespace HolomorphicAnosov

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- If `h` and its derivative are differentiable at `x`, the derivative of
`(x,v) ↦ (h(x), Dh(x)v)` sends `(r,s)` to `(Dh(x)r, D²h(x)(r,v) + Dh(x)s)`.
(Andrews, Lecture 8, Exercise 8.11.3, p. 84) -/
theorem fderiv_tangentTransition_apply {h : E → F} {x : E}
    (hh : DifferentiableAt ℝ h x) (hDh : DifferentiableAt ℝ (fderiv ℝ h) x)
    (v r s : E) :
    fderiv ℝ (fun z : E × E ↦ (h z.1, fderiv ℝ h z.1 z.2)) (x, v) (r, s) =
      (fderiv ℝ h x r, fderiv ℝ (fderiv ℝ h) x r v + fderiv ℝ h x s) := by
  have hfirst := hh.hasFDerivAt.comp (x, v)
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (x, v)))
  have hsecond := (hDh.hasFDerivAt.comp (x, v)
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (x, v)))).clm_apply
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (x, v)))
  simpa [Function.comp_def, add_comm] using
    congrArg (fun L : E × E →L[ℝ] F × F ↦ L (r, s)) (hfirst.prodMk hsecond).fderiv

/-- The Christoffel transition identity implies covariance of the quadratic spray vector.
(Andrews, Lecture 8, Exercises 8.3.2 and 8.11.3, pp. 74, 84) -/
theorem tangentTransition_spray_covariance {h : E → F} {x : E}
    (hh : DifferentiableAt ℝ h x) (hDh : DifferentiableAt ℝ (fderiv ℝ h) x)
    (Γ : E → E → E) (Γ' : F → F → F) (v : E)
    (hΓ : Γ' (fderiv ℝ h x v) (fderiv ℝ h x v) =
      fderiv ℝ h x (Γ v v) - fderiv ℝ (fderiv ℝ h) x v v) :
    fderiv ℝ (fun z : E × E ↦ (h z.1, fderiv ℝ h z.1 z.2)) (x, v) (v, -Γ v v) =
      (fderiv ℝ h x v, -Γ' (fderiv ℝ h x v) (fderiv ℝ h x v)) := by
  rw [fderiv_tangentTransition_apply hh hDh, hΓ, map_neg]
  simp [sub_eq_add_neg, add_comm]

end HolomorphicAnosov

