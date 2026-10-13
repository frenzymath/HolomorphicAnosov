import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# Closedness of the scalar logarithmic differential

For a twice real-differentiable complex-valued gauge function, the one-form
`g⁻¹ dg` has zero exterior derivative wherever `g` is nonzero. This is the
rank-one gauge calculation in Demailly, *Complex Analytic and Differential
Geometry* (2012), V §3, (3.1)–(3.4), p.256, and Zhang §2.1, curvature p.6.
DAG node: `analysis.logarithmic_differential_closed_g7`.
-/

noncomputable section

namespace HolomorphicAnosov

/-- The scalar gauge term has symmetric derivative and hence zero exterior
derivative. The product rule gives `g⁻¹ D²g − g⁻² dg ⊗ dg`. Both terms are
symmetric, the first by equality of mixed second derivatives and the second
by commutativity of complex multiplication. Real differentiability suffices;
neither holomorphicity nor a chosen logarithm is required. -/
theorem logarithmic_differential_closed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℂ} {x : E} (hg : ContDiffAt ℝ 2 g x) (hx : g x ≠ 0) (v w : E) :
    fderiv ℝ (fun y ↦ (g y)⁻¹ • fderiv ℝ g y) x v w -
      fderiv ℝ (fun y ↦ (g y)⁻¹ • fderiv ℝ g y) x w v = 0 := by
  have hd : DifferentiableAt ℝ g x := hg.differentiableAt (by norm_num)
  have hdd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hi := (hasFDerivAt_inv' (𝕜 := ℝ) hx).comp x hd.hasFDerivAt
  have hprod := (hi.smul hdd.hasFDerivAt).fderiv
  change fderiv ℝ (fun y ↦ (g y)⁻¹ • fderiv ℝ g y) x = _ at hprod
  rw [hprod]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    neg_apply, ContinuousLinearMap.mulLeftRight_apply, smul_eq_mul]
  rw [hg.isSymmSndFDerivAt (by norm_num) v w]
  ring

/-- Adding the logarithmic derivative of a nonvanishing scalar gauge does not
change the exterior derivative of a differentiable complex-valued real one-form.
Proof: differentiate the sum, apply closedness of the logarithmic differential,
and cancel its two symmetric directional terms. This is the rank-one form of
the gauge invariance of curvature in Demailly V §3 (3.4), p.256. -/
theorem scalar_gauge_curvature_invariant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : E → E →L[ℝ] ℂ} {g : E → ℂ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hg : ContDiffAt ℝ 2 g x) (hx : g x ≠ 0)
    (v w : E) :
    fderiv ℝ (fun y ↦ A y + (g y)⁻¹ • fderiv ℝ g y) x v w -
      fderiv ℝ (fun y ↦ A y + (g y)⁻¹ • fderiv ℝ g y) x w v =
        fderiv ℝ A x v w - fderiv ℝ A x w v := by
  have hd : DifferentiableAt ℝ g x := hg.differentiableAt (by norm_num)
  have hdd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hG : DifferentiableAt ℝ (fun y ↦ (g y)⁻¹ • fderiv ℝ g y) x :=
    ((hasFDerivAt_inv' (𝕜 := ℝ) hx).comp x hd.hasFDerivAt).differentiableAt.smul hdd
  rw [fderiv_fun_add hA hG]
  simp only [add_apply]
  have h := logarithmic_differential_closed hg hx v w
  linear_combination h

end HolomorphicAnosov


