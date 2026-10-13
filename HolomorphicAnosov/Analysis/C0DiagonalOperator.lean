import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Operator.Bilinear

open scoped ZeroAtInfty BoundedContinuousFunction

namespace HolomorphicAnosov.Analysis

/-- A bounded sequence of linear operators acts diagonally on null sequences.
Source: Wells (1976), p.288, equation (1), order one. The coordinate estimate
`‖a n (w n)‖ ≤ ‖a‖ * ‖w n‖` gives a null output and the operator norm bound. -/
noncomputable def c0DiagonalOperator
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    : (ℕ →ᵇ (E →L[ℝ] F)) →L[ℝ] C₀(ℕ, E) →L[ℝ] C₀(ℕ, F) := by
  let value (a : ℕ →ᵇ (E →L[ℝ] F)) (w : C₀(ℕ, E)) : C₀(ℕ, F) :=
    { toFun := fun n ↦ a n (w n)
      continuous_toFun := continuous_of_discreteTopology
      zero_at_infty' := by
        apply squeeze_zero_norm (fun n ↦
          (a n).le_opNorm (w n) |>.trans
            (mul_le_mul_of_nonneg_right (a.norm_coe_le_norm n) (norm_nonneg _)))
        simpa using (zero_at_infty w).norm.const_mul ‖a‖ }
  let L : (ℕ →ᵇ (E →L[ℝ] F)) →ₗ[ℝ] C₀(ℕ, E) →ₗ[ℝ] C₀(ℕ, F) :=
    { toFun := fun a ↦
        { toFun := value a
          map_add' := fun w z ↦ by ext n; exact map_add (a n) (w n) (z n)
          map_smul' := fun c w ↦ by ext n; exact map_smul (a n) c (w n) }
      map_add' := fun a b ↦ by ext w n; rfl
      map_smul' := fun c a ↦ by ext w n; rfl }
  refine LinearMap.mkContinuous₂ (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜₃ := ℝ)
    (E := ℕ →ᵇ (E →L[ℝ] F)) (F := C₀(ℕ, E)) (G := C₀(ℕ, F))
    (σ₁₃ := RingHom.id ℝ) (σ₂₃ := RingHom.id ℝ) L 1 ?_
  intro a w
  change ‖value a w‖ ≤ 1 * ‖a‖ * ‖w‖
  rw [one_mul, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg a) (norm_nonneg w))).mpr
  intro n
  exact (a n).le_opNorm (w n) |>.trans
    (mul_le_mul (a.norm_coe_le_norm n)
      (BoundedContinuousFunction.norm_coe_le_norm w.toBCF n)
      (norm_nonneg _) (norm_nonneg _))

end HolomorphicAnosov.Analysis

