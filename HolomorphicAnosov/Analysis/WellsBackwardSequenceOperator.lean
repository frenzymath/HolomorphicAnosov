import HolomorphicAnosov.Analysis.WellsBackwardSequenceLinearParts
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.Abel

open scoped ZeroAtInfty ContDiff

namespace HolomorphicAnosov.Analysis

/-- Wells's backward sequence operator from pp.289–290, with a supplied weighted
nonlinear composition C. DAG node: `analysis.wells_backward_sequence_operator_g18`.
Apply the bounded linear and forcing maps to w and C(w).
Continuous linear composition gives smoothness, while the block maximum estimate
and the Lipschitz bound on C give the displayed contraction coefficient. The
zeroth horizontal component vanishes, as needed for complementary Picard iteration.
No regularity outside the original ball or inverse of the second block is used. -/
theorem wells_backward_sequence_operator
    {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    (U : E₁ →L[ℝ] E₁) (V : E₂ →L[ℝ] E₂) (q s ε : ℝ)
    (hq : 0 < q) (r : ℕ∞)
    (C : C₀(ℕ, E₁ × E₂) → C₀(ℕ, E₁ × E₂)) (hC0 : C 0 = 0)
    (hC : ContDiffOn ℝ (r : ℕ∞ω) C (Metric.ball 0 s))
    (hCLip : ∀ w ∈ Metric.ball (0 : C₀(ℕ, E₁ × E₂)) s,
      ∀ z ∈ Metric.ball (0 : C₀(ℕ, E₁ × E₂)) s,
      ‖C w - C z‖ ≤ ε * ‖w - z‖) :
    ∃ Γ : C₀(ℕ, E₁ × E₂) → C₀(ℕ, E₁ × E₂),
      Γ 0 = 0 ∧ ContDiffOn ℝ (r : ℕ∞ω) Γ (Metric.ball 0 s) ∧
      (∀ w, Γ w 0 = (0, q⁻¹ • (V (w 1).2 + (C w 1).2))) ∧
      (∀ w n, Γ w (n + 1) =
        (q • U (w n).1 - U (C w (n + 1)).1,
          q⁻¹ • (V (w (n + 2)).2 + (C w (n + 2)).2))) ∧
      (∀ w ∈ Metric.ball (0 : C₀(ℕ, E₁ × E₂)) s,
        ∀ z ∈ Metric.ball (0 : C₀(ℕ, E₁ × E₂)) s,
        ‖Γ w - Γ z‖ ≤
          max (‖U‖ * (q + ε)) (q⁻¹ * (‖V‖ + ε)) * ‖w - z‖) := by
  obtain ⟨A, B, hzero, hnext, hbound⟩ := wells_backward_sequence_linear_parts U V q hq
  refine ⟨fun w ↦ A w + B (C w), by simp [hC0],
    A.contDiff.contDiffOn.add (hC.continuousLinearMap_comp B),
    (fun w ↦ hzero w (C w)), (fun w n ↦ hnext w (C w) n), ?_⟩
  intro w hw z hz
  have heq : (A w + B (C w)) - (A z + B (C z)) =
      A (w - z) + B (C w - C z) := by simp only [map_sub]; abel
  rw [heq]
  apply (hbound (w - z) (C w - C z)).trans
  apply max_le
  · calc
      ‖U‖ * (q * ‖w - z‖ + ‖C w - C z‖) ≤
          ‖U‖ * (q * ‖w - z‖ + ε * ‖w - z‖) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl (hCLip w hw z hz)) (norm_nonneg U)
      _ = (‖U‖ * (q + ε)) * ‖w - z‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · calc
      q⁻¹ * (‖V‖ * ‖w - z‖ + ‖C w - C z‖) ≤
          q⁻¹ * (‖V‖ * ‖w - z‖ + ε * ‖w - z‖) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl (hCLip w hw z hz)) (inv_nonneg.mpr hq.le)
      _ = (q⁻¹ * (‖V‖ + ε)) * ‖w - z‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

end HolomorphicAnosov.Analysis

