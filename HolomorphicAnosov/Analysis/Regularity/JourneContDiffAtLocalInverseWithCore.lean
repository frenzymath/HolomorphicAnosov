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
import HolomorphicAnosov.Analysis.Regularity.JourneApproximatesLinearImageCore

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation
open Set

open scoped NNReal in
/-- J1's marked inverse has a guarded receiving ball from the same spatial
derivative approximation. The radius and tolerance are selected before any
transverse comparison; no higher transverse derivative is used. -/
theorem contDiffAt_local_inverse_with_core
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} (hn : 1 ≤ n) {f : E → F} {a : E} (A : E ≃L[ℝ] F)
    (hf : ContDiffAt ℝ n f a) (hA : HasFDerivAt f A.toContinuousLinearMap a) :
    ∃ (r : ℝ) (c : ℝ≥0) (e : OpenPartialHomeomorph E F),
      0 < r ∧ 0 < c ∧
      (Subsingleton E ∨ c < ‖A.symm.toContinuousLinearMap‖₊⁻¹) ∧
      (e : E → F) = f ∧ e.source = Metric.ball a r ∧
      Metric.ball (f a)
        (((‖A.symm.toContinuousLinearMap‖₊⁻¹ : ℝ) - (c : ℝ)) * (r / 2)) ⊆
        e.target ∧ a ∈ e.source ∧ ContDiffAt ℝ n e.symm (f a) := by
  have hchoice : ∃ c : ℝ≥0, 0 < c ∧
      (Subsingleton E ∨ c < ‖A.symm.toContinuousLinearMap‖₊⁻¹) := by
    rcases A.subsingleton_or_nnnorm_symm_pos with hsub | hpos
    · exact ⟨1, zero_lt_one, Or.inl hsub⟩
    · exact ⟨‖A.symm.toContinuousLinearMap‖₊⁻¹ / 2,
        half_pos (inv_pos.mpr hpos), Or.inr (half_lt_self (inv_pos.mpr hpos))⟩
  obtain ⟨c, hc, hsmall⟩ := hchoice
  obtain ⟨r, hr, happ⟩ := contDiffAt_approximates_on_ball hn hf hA c hc
  obtain ⟨e, he, hsource, hcore⟩ :=
    approximates_linear_image_core f a A r hr c hsmall happ
  have ha : a ∈ e.source := by rw [hsource]; exact Metric.mem_ball_self hr
  refine ⟨r, c, e, hr, hc, hsmall, he, hsource, hcore, ha, ?_⟩
  have htarget : f a ∈ e.target := by rw [← he]; exact e.map_source ha
  have hinv : e.symm (f a) = a := by rw [← he]; exact e.left_inv ha
  apply e.contDiffAt_symm htarget
  · simpa only [he, hinv] using hA
  · simpa only [he, hinv] using hf

end HolomorphicAnosov.JourneLeafPolynomialApproximation
