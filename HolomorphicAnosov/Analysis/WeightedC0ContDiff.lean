import HolomorphicAnosov.Analysis.C0BoundedComposition
import HolomorphicAnosov.Analysis.NullSequenceUniformContinuity
import Mathlib.Analysis.Calculus.ContDiff.Basic
import HolomorphicAnosov.Analysis.C0BoundedContDiff
import HolomorphicAnosov.Analysis.C0DiagonalOperator
import HolomorphicAnosov.Analysis.WeightedC0HasFDerivAt

namespace HolomorphicAnosov.Analysis

open Filter _root_.Topology
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction

/-- Weighted coordinate superposition on null sequences preserves each positive finite order.
Source: Wells (1976), p.288, Proposition and equation (1). Inverse weights define a
bounded linear self-map of `C₀`, carrying the source ball into itself. Apply bounded
superposition smoothness to `Df`, then compose with this linear scaling map. The
bounded bilinear diagonal operator turns the resulting coefficient sequence into
a `Cⁿ` field of linear maps on `C₀`. The uniform continuity estimate along each
scaled null sequence and the mean-value remainder identify these as the derivatives
of `C`. The successor criterion proves `Cⁿ⁺¹` on the entire original ball. -/
theorem weighted_c0_contDiffOn_succ
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s lam : ℝ) (hs : 0 < s) (hlam : 1 ≤ lam) (n : ℕ) (f : E → F)
    (hf : ContDiffOn ℝ (n + 1) f (Metric.ball 0 s))
    (C : C₀(ℕ, E) → C₀(ℕ, F))
    (hC : ∀ w ∈ Metric.ball (0 : C₀(ℕ, E)) s, ∀ i,
      C w i = (lam ^ i) • f ((lam ^ i)⁻¹ • w i)) :
    ContDiffOn ℝ (n + 1) C (Metric.ball (0 : C₀(ℕ, E)) s) := by
  have hlam0 : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
  have hi (i : ℕ) : 0 ≤ (lam ^ i)⁻¹ := inv_nonneg.mpr (pow_pos hlam0 i).le
  have hib (i : ℕ) : (lam ^ i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hlam)
  have hb (w : C₀(ℕ, E)) (i : ℕ) : ‖(lam ^ i)⁻¹ • w i‖ ≤ ‖w i‖ := by
    rw [norm_smul, Real.norm_of_nonneg (hi i)]
    exact mul_le_of_le_one_left (norm_nonneg _) (hib i)
  let Sₗ : C₀(ℕ, E) →ₗ[ℝ] C₀(ℕ, E) :=
    { toFun := fun w ↦
        { toFun := fun i ↦ (lam ^ i)⁻¹ • w i
          continuous_toFun := continuous_of_discreteTopology
          zero_at_infty' := squeeze_zero_norm (hb w) (by simpa using (zero_at_infty w).norm) }
      map_add' := fun w z ↦ by ext i; exact smul_add _ _ _
      map_smul' := fun c w ↦ by ext i; exact smul_comm _ _ _ }
  have hSbound (w : C₀(ℕ, E)) : ‖Sₗ w‖ ≤ 1 * ‖w‖ := by
    rw [one_mul, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    apply (BoundedContinuousFunction.norm_le (norm_nonneg w)).mpr
    intro i
    exact (hb w i).trans (BoundedContinuousFunction.norm_coe_le_norm w.toBCF i)
  let S : C₀(ℕ, E) →L[ℝ] C₀(ℕ, E) := Sₗ.mkContinuous 1 hSbound
  have hS (w : C₀(ℕ, E)) (hw : w ∈ Metric.ball (0 : C₀(ℕ, E)) s) :
      S w ∈ Metric.ball (0 : C₀(ℕ, E)) s := by
    have : ‖w‖ < s := by simpa using hw
    change ‖Sₗ w‖ < s
    exact (hSbound w).trans_lt (by simpa using this)
  have hder : ContDiffOn ℝ n (fderiv ℝ f) (Metric.ball 0 s) :=
    hf.fderiv_of_isOpen Metric.isOpen_ball le_rfl
  obtain ⟨A, hA⟩ := c0_bounded_composition_exists s hs (fderiv ℝ f) hder.continuousOn
  have hAsmooth := c0_bounded_contDiffOn s hs n (fderiv ℝ f) hder A hA
  have hAS : ContDiffOn ℝ n (A ∘ S) (Metric.ball (0 : C₀(ℕ, E)) s) :=
    (hAsmooth.comp_continuousLinearMap S).mono hS
  let D : C₀(ℕ, E) → C₀(ℕ, E) →L[ℝ] C₀(ℕ, F) := fun w ↦ c0DiagonalOperator (A (S w))
  have hDsmooth : ContDiffOn ℝ n D (Metric.ball (0 : C₀(ℕ, E)) s) := by
    unfold D
    exact ContDiffOn.continuousLinearMap_comp
      (G := C₀(ℕ, E) →L[ℝ] C₀(ℕ, F)) (c0DiagonalOperator (E := E) (F := F)) hAS
  rw [contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn Metric.isOpen_ball.uniqueDiffOn]
  refine ⟨by simp, D, hDsmooth, fun w hw ↦ ?_⟩
  apply HasFDerivAt.hasFDerivWithinAt
  apply weighted_c0_hasFDerivAt s lam hlam f (fderiv ℝ f) ?_ C hC w hw (D w) ?_ ?_
  · intro x hx
    exact (hf.differentiableOn (by simp) x hx).differentiableAt
      (Metric.isOpen_ball.mem_nhds hx) |>.hasFDerivAt
  · intro v i
    change A (S w) i (v i) = _
    rw [hA (S w) (hS w hw) i]
    rfl
  · intro ε hε
    have hg0 : ContinuousAt (fderiv ℝ f) 0 :=
      (hder.continuousOn 0 (by simpa using hs)).continuousAt
        (Metric.isOpen_ball.mem_nhds (by simpa using hs))
    have hgi (i : ℕ) : ContinuousAt (fderiv ℝ f) ((S w) i) := by
      have hiw : (S w) i ∈ Metric.ball (0 : E) s := by
        simpa using (BoundedContinuousFunction.norm_coe_le_norm (S w).toBCF i).trans_lt
          (show ‖S w‖ < s by simpa using hS w hw)
      exact (hder.continuousOn _ hiw).continuousAt (Metric.isOpen_ball.mem_nhds hiw)
    obtain ⟨δ, hδ, hu⟩ := null_sequence_uniform_continuity (fun i ↦ (S w) i)
      (by simpa [cocompact_eq_atTop] using zero_at_infty (S w)) (fderiv ℝ f) hg0 hgi hε
    exact ⟨δ, hδ, fun i y hy ↦ by
      simpa [dist_eq_norm, S, Sₗ] using hu i y (by simpa [dist_eq_norm, S, Sₗ] using hy)⟩

end HolomorphicAnosov.Analysis

