import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Group.Constructions

open Filter
open scoped Topology _root_.Topology

namespace HolomorphicAnosov

/-- For two points in the original ball, the remainder bound gives the corresponding horizontal and vertical component estimates. (HPS, §5.1, p. 58) -/
theorem hps_local_component_estimates
    {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    (T₁ : E₁ ≃L[ℝ] E₁) (T₂ : E₂ →L[ℝ] E₂)
    (g : E₁ × E₂ → E₁ × E₂) (s ε : ℝ)
    (ha : ‖T₁.symm.toContinuousLinearMap‖ ≠ 0)
    (hR : ∀ z ∈ Metric.ball (0 : E₁ × E₂) s,
      ∀ z' ∈ Metric.ball (0 : E₁ × E₂) s,
      ‖(g z - (T₁ z.1, T₂ z.2)) - (g z' - (T₁ z'.1, T₂ z'.2))‖ ≤
        ε * ‖z - z'‖)
    (z z' : E₁ × E₂) (hz : z ∈ Metric.ball 0 s) (hz' : z' ∈ Metric.ball 0 s) :
    ‖T₁.symm.toContinuousLinearMap‖⁻¹ * ‖z.1 - z'.1‖ ≤
        ‖(g z).1 - (g z').1‖ + ε * ‖z - z'‖ ∧
      ‖(g z).2 - (g z').2‖ ≤ ‖T₂‖ * ‖z.2 - z'.2‖ + ε * ‖z - z'‖ := by
  have h₁ := (norm_fst_le
    ((g z - (T₁ z.1, T₂ z.2)) - (g z' - (T₁ z'.1, T₂ z'.2)))).trans
      (hR z hz z' hz')
  have h₂ := (norm_snd_le
    ((g z - (T₁ z.1, T₂ z.2)) - (g z' - (T₁ z'.1, T₂ z'.2)))).trans
      (hR z hz z' hz')
  change ‖((g z).1 - T₁ z.1) - ((g z').1 - T₁ z'.1)‖ ≤ ε * ‖z - z'‖ at h₁
  change ‖((g z).2 - T₂ z.2) - ((g z').2 - T₂ z'.2)‖ ≤ ε * ‖z - z'‖ at h₂
  constructor
  · have hlin : ‖z.1 - z'.1‖ ≤
        ‖T₁.symm.toContinuousLinearMap‖ * ‖T₁ (z.1 - z'.1)‖ := by
      simpa using T₁.symm.toContinuousLinearMap.le_opNorm (T₁ (z.1 - z'.1))
    have hT : ‖T₁ (z.1 - z'.1)‖ ≤ ‖(g z).1 - (g z').1‖ + ε * ‖z - z'‖ := by
      calc
        _ = ‖((g z).1 - (g z').1) -
            (((g z).1 - T₁ z.1) - ((g z').1 - T₁ z'.1))‖ := by
          congr 1
          rw [map_sub]
          abel
        _ ≤ _ := (norm_sub_le _ _).trans (add_le_add le_rfl h₁)
    rw [inv_mul_eq_div]
    exact (div_le_iff₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm ha))).mpr
      (by simpa [mul_comm] using hlin.trans (mul_le_mul_of_nonneg_left hT (norm_nonneg _)))
  · calc
      _ = ‖T₂ (z.2 - z'.2) +
          (((g z).2 - T₂ z.2) - ((g z').2 - T₂ z'.2))‖ := by
        congr 1
        rw [map_sub]
        abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (T₂.le_opNorm _) h₂)

end HolomorphicAnosov
