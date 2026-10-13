import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.WedgeApplyNormLe
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

open scoped Manifold ContDiff Topology _root_.Topology
open Filter MeasureTheory TopologicalSpace Set
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
namespace HolomorphicAnosov
namespace ConnectionFlatEstimates
open scoped BigOperators

/-- The sum of squared wedge coefficients on `r` unit vectors is at most `4 * r ^ 2 * ‖b‖ ^ 2 * ‖c‖
^ 2`. (Zhang, eq. (8)) -/
theorem wedge_sum_sq_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℕ} (e : Fin r → E) (he : ∀ i, ‖e i‖ = 1) (b c : E →L[ℝ] ℂ) :
    ∑ i : Fin r, ∑ j : Fin r, ‖b (e i) * c (e j) - b (e j) * c (e i)‖ ^ 2 ≤
      4 * (r : ℝ) ^ 2 * ‖b‖ ^ 2 * ‖c‖ ^ 2 := by
  have hbound (i j : Fin r) :
      ‖b (e i) * c (e j) - b (e j) * c (e i)‖ ^ 2 ≤
        (2 * ‖b‖ * ‖c‖) ^ 2 := by
    apply pow_le_pow_left₀ (norm_nonneg _)
    simpa only [he, mul_one] using wedge_apply_norm_le b c (e i) (e j)
  calc
    _ ≤ ∑ i : Fin r, ∑ j : Fin r, (2 * ‖b‖ * ‖c‖) ^ 2 :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hbound i j
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end ConnectionFlatEstimates
end HolomorphicAnosov
