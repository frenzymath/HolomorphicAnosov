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

open scoped Topology NNReal in
/-- Source: J1, continuity of the first derivative of the marked-plaque map.
On a small actual open ball all derivatives are close to the marked derivative.
This is the derivative-bound premise of the mean-value step, not its conclusion. -/
theorem contDiffAt_derivative_close_on_ball
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} (hn : 1 ≤ n) {f : E → F} {a : E} {A : E →L[ℝ] F}
    (hf : ContDiffAt ℝ n f a) (hA : HasFDerivAt f A a)
    (c : ℝ≥0) (hc : 0 < c) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ Metric.ball a r,
      DifferentiableAt ℝ f y ∧ ‖fderiv ℝ f y - A‖ < (c : ℝ) := by
  have hn' : (1 : WithTop ℕ∞) ≤ n := by exact_mod_cast hn
  rcases hf.of_le hn' 1 le_rfl with ⟨u, hu, p, hp⟩
  simp only [Set.mem_univ, Set.insert_eq_of_mem, nhdsWithin_univ] at hu
  let D : E → E →L[ℝ] F := fun y ↦ continuousMultilinearCurryFin1 ℝ E F (p y 1)
  have hD : ∀ᶠ y in 𝓝 a, HasFDerivAt f (D y) y :=
    hp.eventually_hasFDerivAt one_ne_zero hu
  have hDc : ContinuousAt D a :=
    (continuousMultilinearCurryFin1 ℝ E F).continuousAt.comp
      ((hp.cont 1 le_rfl).continuousAt hu)
  have hDa : D a = A := (hD.self_of_nhds.fderiv).symm.trans hA.fderiv
  have hb : ∀ᶠ y in 𝓝 a, ‖D y - A‖ < (c : ℝ) := by
    have hpos : ‖D a - A‖ < (c : ℝ) := by simpa [hDa] using hc
    exact (hDc.sub_const A).norm.eventually (gt_mem_nhds hpos)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hD.and hb)
  refine ⟨r, hr, ?_⟩
  intro y hy
  exact ⟨(hball hy).1.differentiableAt, by
    rw [(hball hy).1.fderiv]
    exact (hball hy).2⟩

end HolomorphicAnosov.JourneLeafPolynomialApproximation
