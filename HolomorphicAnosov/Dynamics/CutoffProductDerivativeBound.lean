import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# A uniform derivative bound for a cutoff product

Source: Merry, *Sixty Lectures on Dynamical Systems*, Lecture 32, Theorem 32.2,
local pp. 5–6, equations (32.6)–(32.7), retaining an arbitrary finite bump bound.
-/

namespace HolomorphicAnosov.ExponentialCutoff

open Set Metric
open scoped Topology _root_.Topology

/-- A cutoff product is differentiable everywhere with derivative norm at most `(1 + K) * η`.

Proof: the mean value estimate on the closed radius-`δ` ball gives
`‖q x‖ ≤ η * ‖x‖`. On that ball the product rule bounds its two derivative terms
by `η` and `(K / δ) * (η * δ) = K * η`. Outside the ball the cutoff is locally zero,
so no exterior regularity of `q` is needed. The boundary uses the given derivatives
on the closed ball. Source: Merry, Lecture 32, equations (32.6)–(32.7). -/
theorem cutoff_product_derivative_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (χ : E → ℝ) (q : E → F) {δ K η : ℝ}
    (hδ : 0 < δ) (hK : 0 ≤ K) (hη : 0 ≤ η)
    (hχ : Differentiable ℝ χ)
    (hχbound : ∀ x, ‖χ x‖ ≤ 1)
    (hχderiv : ∀ x, ‖x‖ ≤ δ → ‖fderiv ℝ χ x‖ ≤ K / δ)
    (hχzero : ∀ x, δ < ‖x‖ → χ x = 0)
    (hqzero : q 0 = 0)
    (hq : ∀ x, ‖x‖ ≤ δ → DifferentiableAt ℝ q x)
    (hqderiv : ∀ x, ‖x‖ ≤ δ → ‖fderiv ℝ q x‖ ≤ η)
    (x : E) :
    DifferentiableAt ℝ (fun y ↦ χ y • q y) x ∧
      ‖fderiv ℝ (fun y ↦ χ y • q y) x‖ ≤ (1 + K) * η := by
  have hproduct : ∃ D : E →L[ℝ] F,
      HasFDerivAt (fun y ↦ χ y • q y) D x ∧ ‖D‖ ≤ (1 + K) * η := by
    by_cases hx : ‖x‖ ≤ δ
    · have hqbound : ‖q x‖ ≤ η * ‖x‖ := by
        have := (convex_closedBall (0 : E) δ).norm_image_sub_le_of_norm_fderiv_le
          (fun y hy ↦ hq y (by simpa using hy))
          (fun y hy ↦ hqderiv y (by simpa using hy))
          (show (0 : E) ∈ closedBall 0 δ by simp [hδ.le])
          (show x ∈ closedBall 0 δ by simpa using hx)
        simpa [hqzero] using this
      refine ⟨χ x • fderiv ℝ q x + (fderiv ℝ χ x).smulRight (q x),
        (hχ x).hasFDerivAt.smul (hq x hx).hasFDerivAt, ?_⟩
      have hfirst : ‖χ x • fderiv ℝ q x‖ ≤ η := by
        rw [norm_smul]
        exact (mul_le_mul (hχbound x) (hqderiv x hx) (norm_nonneg _)
          (by norm_num)).trans_eq (one_mul η)
      have hsecond : ‖(fderiv ℝ χ x).smulRight (q x)‖ ≤ K * η := by
        rw [ContinuousLinearMap.norm_smulRight_apply]
        calc
          ‖fderiv ℝ χ x‖ * ‖q x‖ ≤ (K / δ) * (η * δ) :=
            mul_le_mul (hχderiv x hx)
              ((hqbound).trans (mul_le_mul_of_nonneg_left hx hη))
              (norm_nonneg _) (div_nonneg hK hδ.le)
          _ = K * η := by field_simp
      calc
        _ ≤ ‖χ x • fderiv ℝ q x‖ + ‖(fderiv ℝ χ x).smulRight (q x)‖ :=
          norm_add_le _ _
        _ ≤ η + K * η := add_le_add hfirst hsecond
        _ = (1 + K) * η := by ring
    · have hx' : δ < ‖x‖ := lt_of_not_ge hx
      have heq : (fun y ↦ χ y • q y) =ᶠ[𝓝 x] fun _ ↦ (0 : F) := by
        filter_upwards [isOpen_lt continuous_const continuous_norm |>.mem_nhds hx'] with y hy
        simp [hχzero y hy]
      exact ⟨0, (hasFDerivAt_const (0 : F) x).congr_of_eventuallyEq heq,
        by simpa using mul_nonneg (by linarith : 0 ≤ 1 + K) hη⟩
  obtain ⟨D, hD, hDbound⟩ := hproduct
  exact ⟨hD.differentiableAt, by simpa only [hD.fderiv] using hDbound⟩


end HolomorphicAnosov.ExponentialCutoff
