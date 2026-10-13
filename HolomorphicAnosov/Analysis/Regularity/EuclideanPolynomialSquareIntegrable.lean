import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Finite polynomial square integrals on bounded Euclidean subsets

Source: Campanato (1964), Lemma [2.I], pp.140–143: bounded-domain polynomial
integrals are finite. No measurability condition on the subset is needed because
restriction of an integrable function remains integrable on every subset.
-/

open MeasureTheory
namespace HolomorphicAnosov.Analysis.Regularity

/-- Source: Campanato (1964), Lemma [2.I], pp.140–143. Polynomial evaluation is
continuous in Euclidean coordinates, so its squared absolute value is integrable
on the compact closed ball. Restrict this integral to E. Volume monotonicity
and finite ball volume give the finite-measure assertion. Dimension zero and
empty sets are included; no degree bound is necessary. -/
theorem euclidean_polynomial_square_integrable {N : ℕ} (P : MvPolynomial (Fin N) ℝ)
    (a : EuclideanSpace ℝ (Fin N)) (ρ : ℝ)
    (E : Set (EuclideanSpace ℝ (Fin N))) (hE : E ⊆ Metric.ball a ρ) :
    volume E < ⊤ ∧
      IntegrableOn (fun x ↦ |MvPolynomial.eval (fun i ↦ x i) P| ^ 2) E volume := by
  refine ⟨(measure_mono hE).trans_lt measure_ball_lt_top, ?_⟩
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin N) ↦
      |MvPolynomial.eval (fun i ↦ x i) P| ^ 2) :=
    ((AnalyticOnNhd.eval_continuousLinearMap'
      (fun i : Fin N ↦ PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N ↦ ℝ) i) P).continuous.abs).pow 2
  exact (hc.continuousOn.integrableOn_compact (isCompact_closedBall a ρ)).mono_set
    (hE.trans Metric.ball_subset_closedBall)

end HolomorphicAnosov.Analysis.Regularity
