import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Tactic.Abel

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation

/-- The derivative of a recharted plaque remains close to its marked linear inclusion when both the inverse derivative and the plaque derivative remain close to their marked values. (Journé, 1988) -/
theorem recharted_plaque_derivative_close
    {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → F) (q : D → E) (a : E) (x : D)
    (Q₀ : D →L[ℝ] E) (I : D →L[ℝ] F) (A B ε δ : ℝ)
    (hε : 0 ≤ ε) (hA : 0 ≤ A)
    (hg : DifferentiableAt ℝ g (q x)) (hq : DifferentiableAt ℝ q x)
    (hmarked : (fderiv ℝ g a).comp Q₀ = I)
    (hginv : ‖fderiv ℝ g a‖ ≤ A)
    (hqbound : ‖fderiv ℝ q x‖ ≤ B)
    (hgclose : ‖fderiv ℝ g (q x) - fderiv ℝ g a‖ ≤ ε)
    (hqclose : ‖fderiv ℝ q x - Q₀‖ ≤ δ) :
    ‖fderiv ℝ (g ∘ q) x - I‖ ≤ ε * B + A * δ := by
  rw [fderiv_comp x hg hq, ← hmarked]
  have heq : (fderiv ℝ g (q x)).comp (fderiv ℝ q x) -
      (fderiv ℝ g a).comp Q₀ =
      (fderiv ℝ g (q x) - fderiv ℝ g a).comp (fderiv ℝ q x) +
      (fderiv ℝ g a).comp (fderiv ℝ q x - Q₀) := by
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    abel
  rw [heq]
  calc
    _ ≤ ‖(fderiv ℝ g (q x) - fderiv ℝ g a).comp (fderiv ℝ q x)‖ +
        ‖(fderiv ℝ g a).comp (fderiv ℝ q x - Q₀)‖ := norm_add_le _ _
    _ ≤ ‖fderiv ℝ g (q x) - fderiv ℝ g a‖ * ‖fderiv ℝ q x‖ +
        ‖fderiv ℝ g a‖ * ‖fderiv ℝ q x - Q₀‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
        (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ _ := add_le_add
      (mul_le_mul hgclose hqbound (norm_nonneg _) hε)
      (mul_le_mul hginv hqclose (norm_nonneg _) hA)

end HolomorphicAnosov.JourneLeafPolynomialApproximation
