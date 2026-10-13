import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

noncomputable section
universe u
namespace HolomorphicAnosov
namespace ConnectionFlatEstimates

/-- The wedge evaluation `b v * c w - b w * c v` has norm at most `2 * ‖b‖ * ‖c‖ * ‖v‖ * ‖w‖`.
(Zhang, eq. (8)) -/
theorem wedge_apply_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b c : E →L[ℝ] ℂ) (v w : E) :
    ‖b v * c w - b w * c v‖ ≤ 2 * ‖b‖ * ‖c‖ * ‖v‖ * ‖w‖ := by
  calc
    ‖b v * c w - b w * c v‖ ≤ ‖b v * c w‖ + ‖b w * c v‖ := norm_sub_le _ _
    _ = ‖b v‖ * ‖c w‖ + ‖b w‖ * ‖c v‖ := by rw [norm_mul, norm_mul]
    _ ≤ (‖b‖ * ‖v‖) * (‖c‖ * ‖w‖) +
        (‖b‖ * ‖w‖) * (‖c‖ * ‖v‖) := by
      apply add_le_add
      · exact mul_le_mul (b.le_opNorm v) (c.le_opNorm w) (norm_nonneg _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      · exact mul_le_mul (b.le_opNorm w) (c.le_opNorm v) (norm_nonneg _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

end ConnectionFlatEstimates
end HolomorphicAnosov

