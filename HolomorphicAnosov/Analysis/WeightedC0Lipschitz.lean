import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Tactic.FieldSimp

open scoped ZeroAtInfty

namespace HolomorphicAnosov.Analysis

/-- The weighted null-sequence composition of a centered Lipschitz map exists and
has the same Lipschitz bound on the original ball. Source: Wells (1976), pp.287–288,
definition and first sentence of the Proposition's proof. Inverse weights keep
all arguments in the source ball. The output bound by `L * ‖w n‖` proves vanishing
at infinity, and taking the supremum of the coordinate difference bounds gives
the stated Lipschitz estimate. No derivative or whole-ball derivative bound is used. -/
theorem weighted_c0_lipschitz
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s lam L : ℝ) (f : E → F)
    (hs : 0 < s) (hlam : 1 ≤ lam) (hL : 0 ≤ L)
    (hf_zero : f 0 = 0)
    (hf_lipschitz : ∀ x ∈ Metric.ball (0 : E) s, ∀ y ∈ Metric.ball (0 : E) s,
      ‖f x - f y‖ ≤ L * ‖x - y‖) :
    ∃ C : C₀(ℕ, E) → C₀(ℕ, F),
      (∀ w ∈ Metric.ball (0 : C₀(ℕ, E)) s, ∀ n : ℕ,
        C w n = (lam ^ n) • f ((lam ^ n)⁻¹ • w n)) ∧
      C 0 = 0 ∧
      (∀ w ∈ Metric.ball (0 : C₀(ℕ, E)) s,
        ∀ z ∈ Metric.ball (0 : C₀(ℕ, E)) s, ‖C w - C z‖ ≤ L * ‖w - z‖) := by
  classical
  have hlam0 : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
  have hpowpos (n : ℕ) : 0 < lam ^ n := pow_pos hlam0 n
  have hpowone (n : ℕ) : 1 ≤ lam ^ n := one_le_pow₀ hlam
  have hcoord (w : C₀(ℕ, E)) (n : ℕ) : ‖w n‖ ≤ ‖w‖ :=
    BoundedContinuousFunction.norm_coe_le_norm w.toBCF n
  have hscaled (w : C₀(ℕ, E)) (hw : w ∈ Metric.ball (0 : C₀(ℕ, E)) s) (n : ℕ) :
      (lam ^ n)⁻¹ • w n ∈ Metric.ball (0 : E) s := by
    rw [Metric.mem_ball, dist_zero_right] at hw ⊢
    calc
      ‖(lam ^ n)⁻¹ • w n‖ = (lam ^ n)⁻¹ * ‖w n‖ := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hpowpos n).le)]
      _ ≤ 1 * ‖w n‖ := mul_le_mul_of_nonneg_right
        (inv_le_one_of_one_le₀ (hpowone n)) (norm_nonneg _)
      _ ≤ ‖w‖ := by simpa using hcoord w n
      _ < s := hw
  have hscaledLip (w z : C₀(ℕ, E))
      (hw : w ∈ Metric.ball (0 : C₀(ℕ, E)) s)
      (hz : z ∈ Metric.ball (0 : C₀(ℕ, E)) s) (n : ℕ) :
      ‖(lam ^ n) • f ((lam ^ n)⁻¹ • w n) -
        (lam ^ n) • f ((lam ^ n)⁻¹ • z n)‖ ≤ L * ‖w n - z n‖ := by
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hpowpos n).le]
    calc
      lam ^ n * ‖f ((lam ^ n)⁻¹ • w n) - f ((lam ^ n)⁻¹ • z n)‖ ≤
          lam ^ n * (L * ‖(lam ^ n)⁻¹ • w n - (lam ^ n)⁻¹ • z n‖) :=
        mul_le_mul_of_nonneg_left
          (hf_lipschitz _ (hscaled w hw n) _ (hscaled z hz n)) (hpowpos n).le
      _ = L * ‖w n - z n‖ := by
        rw [← smul_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hpowpos n).le)]
        field_simp
  have hzero : (0 : C₀(ℕ, E)) ∈ Metric.ball (0 : C₀(ℕ, E)) s := by
    simpa using hs
  have hbound (w : C₀(ℕ, E)) (hw : w ∈ Metric.ball (0 : C₀(ℕ, E)) s) (n : ℕ) :
      ‖(lam ^ n) • f ((lam ^ n)⁻¹ • w n)‖ ≤ L * ‖w n‖ := by
    simpa [hf_zero] using hscaledLip w 0 hw hzero n
  let C : C₀(ℕ, E) → C₀(ℕ, F) := fun w ↦
    if hw : w ∈ Metric.ball (0 : C₀(ℕ, E)) s then
      { toFun := fun n ↦ (lam ^ n) • f ((lam ^ n)⁻¹ • w n)
        continuous_toFun := continuous_of_discreteTopology
        zero_at_infty' := by
          apply squeeze_zero_norm (hbound w hw)
          simpa using (zero_at_infty w).norm.const_mul L }
    else 0
  have hformula (w : C₀(ℕ, E)) (hw : w ∈ Metric.ball (0 : C₀(ℕ, E)) s) (n : ℕ) :
      C w n = (lam ^ n) • f ((lam ^ n)⁻¹ • w n) := by
    simp only [C, dite_eq_left hw, ZeroAtInftyContinuousMap.coe_mk]
  refine ⟨C, hformula, ?_, ?_⟩
  · apply ZeroAtInftyContinuousMap.ext
    intro n
    simp [hformula _ hzero n, hf_zero]
  · intro w hw z hz
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    apply (BoundedContinuousFunction.norm_le (mul_nonneg hL (norm_nonneg _))).mpr
    intro n
    change ‖C w n - C z n‖ ≤ _
    rw [hformula w hw n, hformula z hz n]
    exact (hscaledLip w z hw hz n).trans
      (mul_le_mul_of_nonneg_left (hcoord (w - z) n) hL)

end HolomorphicAnosov.Analysis

