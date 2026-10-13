import HolomorphicAnosov.Analysis.BilinearHolderBound
import HolomorphicAnosov.Analysis.CompositionHolderBound
import HolomorphicAnosov.Analysis.Regularity.PolynomialBallDerivativeEstimate
import HolomorphicAnosov.Analysis.Regularity.PolynomialMeasurableSubsetDerivativeEstimate
import HolomorphicAnosov.Analysis.WellsLipschitzPerturbationSmoothInverse
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import HolomorphicAnosov.Analysis.Regularity.GraphFoliationData
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.Prod

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation
open Set

open scoped NNReal in
/-- J1: two plaque approximation bounds combine in the original product maximum norm. -/
theorem plaque_sum_approximates
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {P : E → G} {Q : F → G} {D₁ : E →L[ℝ] G} {D₂ : F →L[ℝ] G}
    {x : E} {y : F} {r : ℝ} {c : ℝ≥0}
    (hP : ApproximatesLinearOn P D₁ (Metric.ball x r) c)
    (hQ : ApproximatesLinearOn Q D₂ (Metric.ball y r) c) (a : G) :
    ApproximatesLinearOn (fun z : E × F ↦ P z.1 + Q z.2 - a)
      (D₁.coprod D₂) (Metric.ball (x, y) r) (c + c) := by
  intro z hz w hw
  simp only [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hz hw
  have hsum : P z.1 + Q z.2 - a - (P w.1 + Q w.2 - a) -
      (D₁.coprod D₂) (z - w) =
      (P z.1 - P w.1 - D₁ (z.1 - w.1)) + (Q z.2 - Q w.2 - D₂ (z.2 - w.2)) := by
    simp only [ContinuousLinearMap.coprod_apply, Prod.fst_sub, Prod.snd_sub]
    abel
  rw [hsum]
  calc
    _ ≤ ‖P z.1 - P w.1 - D₁ (z.1 - w.1)‖ +
        ‖Q z.2 - Q w.2 - D₂ (z.2 - w.2)‖ := norm_add_le _ _
    _ ≤ c * ‖z.1 - w.1‖ + c * ‖z.2 - w.2‖ :=
      add_le_add (hP z.1 hz.1 w.1 hw.1) (hQ z.2 hz.2 w.2 hw.2)
    _ ≤ c * ‖z - w‖ + c * ‖z - w‖ := add_le_add
      (mul_le_mul_of_nonneg_left (norm_fst_le (z - w)) c.2)
      (mul_le_mul_of_nonneg_left (norm_snd_le (z - w)) c.2)
    _ = ((c + c : ℝ≥0) : ℝ) * ‖z - w‖ := by rw [NNReal.coe_add, add_mul]

end HolomorphicAnosov.JourneLeafPolynomialApproximation
