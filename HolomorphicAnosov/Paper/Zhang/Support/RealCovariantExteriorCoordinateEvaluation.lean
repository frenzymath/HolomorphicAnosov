import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-! Real-coordinate expansion of the covariant exterior expression with the Bott bracket. (Zhang,
eqs. (12)–(13)) -/
noncomputable section
namespace HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport

/-- The covariant exterior expression with the half real-minus-imaginary Bott bracket equals the
antisymmetric derivative of the one-form plus the connection wedge term. (Zhang, eqs. (12)–(13),
p. 7, eq. (2), p. 4) -/
theorem real_covariant_exterior_coordinate_evaluation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    (θ : E → E →L[ℂ] ℂ) (A : E →L[ℝ] ℂ) (Y Z : E → E) {z : E}
    (Dθ : E →L[ℂ] (E →L[ℂ] ℂ)) (hθ : HasFDerivAt θ Dθ z)
    (hAI : ∀ v, A (Complex.I • v) = Complex.I * A v)
    (hY : DifferentiableAt ℝ Y z) (hZ : DifferentiableAt ℝ Z z) :
    (1 / 2 : ℂ) *
        (fderiv ℝ (fun y ↦ θ y (Z y)) z (Y z) + A (Y z) * θ z (Z z) -
          Complex.I * (fderiv ℝ (fun y ↦ θ y (Z y)) z (Complex.I • Y z) +
            A (Complex.I • Y z) * θ z (Z z))) -
      (1 / 2 : ℂ) *
        (fderiv ℝ (fun y ↦ θ y (Y y)) z (Z z) + A (Z z) * θ z (Y z) -
          Complex.I * (fderiv ℝ (fun y ↦ θ y (Y y)) z (Complex.I • Z z) +
            A (Complex.I • Z z) * θ z (Y z))) -
      θ z ((1 / 2 : ℝ) • (VectorField.lieBracket ℝ Y Z z -
        VectorField.lieBracket ℝ (fun y ↦ Complex.I • Y y) (fun y ↦ Complex.I • Z y) z)) =
      fderiv ℝ θ z (Y z) (Z z) - fderiv ℝ θ z (Z z) (Y z) +
        A (Y z) * θ z (Z z) - A (Z z) * θ z (Y z) := by
  have hθR := hθ.restrictScalars ℝ
  have hθ' := (ContinuousLinearMap.restrictScalarsL ℂ E ℂ ℝ ℝ).hasFDerivAt.comp z hθR
  have hEvalY := (hθ'.clm_apply hY.hasFDerivAt).fderiv
  have hEvalZ := (hθ'.clm_apply hZ.hasFDerivAt).fderiv
  have hIY : fderiv ℝ (fun y ↦ Complex.I • Y y) z = Complex.I • fderiv ℝ Y z :=
    (hY.hasFDerivAt.const_smul Complex.I).fderiv
  have hIZ : fderiv ℝ (fun y ↦ Complex.I • Z y) z = Complex.I • fderiv ℝ Z z :=
    (hZ.hasFDerivAt.const_smul Complex.I).fderiv
  simp only [Function.comp_apply, ContinuousLinearMap.coe_restrict_scalarsL',
    ContinuousLinearMap.coe_restrictScalars'] at hEvalY hEvalZ
  rw [hEvalY, hEvalZ, hθR.fderiv]
  simp only [VectorField.lieBracket]
  rw [hIY, hIZ]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.coe_restrict_scalarsL',
    smul_apply, map_smul, hAI, smul_eq_mul]
  simp only [ContinuousLinearMap.map_smul_of_tower, map_sub, map_smul, smul_eq_mul,
    Complex.real_smul]
  ring_nf
  simp [Complex.I_sq]
  ring

end HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport

