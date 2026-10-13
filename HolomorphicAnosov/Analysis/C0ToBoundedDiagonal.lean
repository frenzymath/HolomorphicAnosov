import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Operator.Bilinear

open scoped ZeroAtInfty BoundedContinuousFunction

namespace HolomorphicAnosov.Analysis

/-- Bounded operator coefficients act on null sequences to give bounded sequences.
Source: Wells (1976), p.288, equation (1), order one, using the same supremum estimate
in the bounded-sequence codomain. Coordinatewise linearity in coefficients and inputs
and the estimate `‖a n (w n)‖ ≤ ‖a‖ * ‖w‖` give a continuous bilinear map. -/
noncomputable def c0ToBoundedDiagonal
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    (ℕ →ᵇ (E →L[ℝ] F)) →L[ℝ] C₀(ℕ, E) →L[ℝ] (ℕ →ᵇ F) := by
  let value (a : ℕ →ᵇ (E →L[ℝ] F)) (w : C₀(ℕ, E)) : ℕ →ᵇ F :=
    BoundedContinuousFunction.mkOfDiscrete (fun n ↦ a n (w n)) (2 * (‖a‖ * ‖w‖))
      (fun n m ↦ by
        calc
          dist (a n (w n)) (a m (w m)) ≤ ‖a n (w n)‖ + ‖a m (w m)‖ := dist_le_norm_add_norm _ _
          _ ≤ ‖a‖ * ‖w‖ + ‖a‖ * ‖w‖ := add_le_add
            ((a n).le_opNorm _ |>.trans (mul_le_mul (a.norm_coe_le_norm n)
              (BoundedContinuousFunction.norm_coe_le_norm w.toBCF n)
              (norm_nonneg _) (norm_nonneg a)))
            ((a m).le_opNorm _ |>.trans (mul_le_mul (a.norm_coe_le_norm m)
              (BoundedContinuousFunction.norm_coe_le_norm w.toBCF m)
              (norm_nonneg _) (norm_nonneg a)))
          _ = _ := by ring)
  let L : (ℕ →ᵇ (E →L[ℝ] F)) →ₗ[ℝ] C₀(ℕ, E) →ₗ[ℝ] (ℕ →ᵇ F) :=
    { toFun := fun a ↦
        { toFun := value a
          map_add' := fun w z ↦ by ext n; exact map_add (a n) _ _
          map_smul' := fun c w ↦ by ext n; exact map_smul (a n) c _ }
      map_add' := fun a b ↦ by ext w n; rfl
      map_smul' := fun c a ↦ by ext w n; rfl }
  refine LinearMap.mkContinuous₂ (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜₃ := ℝ)
    (E := ℕ →ᵇ (E →L[ℝ] F)) (F := C₀(ℕ, E)) (G := ℕ →ᵇ F)
    (σ₁₃ := RingHom.id ℝ) (σ₂₃ := RingHom.id ℝ) L 1 ?_
  intro a w
  change ‖value a w‖ ≤ 1 * ‖a‖ * ‖w‖
  exact (by
    simp only [one_mul]
    apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg a) (norm_nonneg w))).mpr
    intro n
    exact (a n).le_opNorm _ |>.trans (mul_le_mul (a.norm_coe_le_norm n)
      (BoundedContinuousFunction.norm_coe_le_norm w.toBCF n)
              (norm_nonneg _) (norm_nonneg a)))

end HolomorphicAnosov.Analysis

