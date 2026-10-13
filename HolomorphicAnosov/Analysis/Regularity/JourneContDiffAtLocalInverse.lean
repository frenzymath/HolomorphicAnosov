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
import HolomorphicAnosov.Analysis.Regularity.JourneContDiffAtApproximatesOnBall

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation
open Set

open scoped NNReal in
/-- Source: J1 and the inverse step of J2. The map with invertible marked
differential has an actual open local inverse, smooth at the marked image.
The map and its inverse retain their original Banach-space carriers. -/
theorem contDiffAt_local_inverse
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} (hn : 1 ≤ n) {f : E → F} {a : E} (A : E ≃L[ℝ] F)
    (hf : ContDiffAt ℝ n f a) (hA : HasFDerivAt f A.toContinuousLinearMap a) :
    ∃ e : OpenPartialHomeomorph E F,
      (e : E → F) = f ∧ a ∈ e.source ∧
      ContDiffAt ℝ n e.symm (f a) := by
  have hchoice : ∃ c : ℝ≥0, 0 < c ∧
      (Subsingleton E ∨ c < ‖A.symm.toContinuousLinearMap‖₊⁻¹) := by
    rcases A.subsingleton_or_nnnorm_symm_pos with hsub | hpos
    · exact ⟨1, zero_lt_one, Or.inl hsub⟩
    · exact ⟨‖A.symm.toContinuousLinearMap‖₊⁻¹ / 2,
        half_pos (inv_pos.mpr hpos), Or.inr (half_lt_self (inv_pos.mpr hpos))⟩
  obtain ⟨c, hc, hsmall⟩ := hchoice
  obtain ⟨r, hr, happ⟩ := contDiffAt_approximates_on_ball hn hf hA c hc
  let e := happ.toOpenPartialHomeomorph f (Metric.ball a r) hsmall Metric.isOpen_ball
  have he : (e : E → F) = f := rfl
  have ha : a ∈ e.source := by exact Metric.mem_ball_self hr
  refine ⟨e, he, ha, ?_⟩
  have htarget : f a ∈ e.target := e.map_source ha
  have hinv : e.symm (f a) = a := e.left_inv ha
  apply e.contDiffAt_symm htarget
  · simpa only [he, hinv] using hA
  · simpa only [he, hinv] using hf

end HolomorphicAnosov.JourneLeafPolynomialApproximation
