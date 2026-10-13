import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic.FieldSimp

namespace HolomorphicAnosov.Analysis

/-- Multiplying Wells's component equations (3), (3′), pp.290, yields the
backward physical recurrence. DAG node: `analysis.wells_backward_weighted_recurrence_g18`.
The printed equation (4) has the direction reversed;
the component equations give g(q⁻ⁿ⁻¹wₙ₊₁)=q⁻ⁿwₙ. Apply the first linear block to
the horizontal equation and multiply the vertical equation by q. Their combined
equation is T(wₙ₊₁)+cₙ₊₁=q wₙ. The weighted remainder identity and linearity
then cancel qⁿ⁺¹, giving the claimed recurrence. -/
theorem wells_backward_weighted_recurrence
    {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    (T₁ : E₁ ≃L[ℝ] E₁) (T₂ : E₂ →L[ℝ] E₂)
    (q : ℝ) (hq : q ≠ 0) (g R : (E₁ × E₂) → (E₁ × E₂))
    (hR : ∀ z, g z = (T₁ z.1, T₂ z.2) + R z)
    (w c : ℕ → E₁ × E₂)
    (hc : ∀ n, c n = q ^ n • R ((q ^ n)⁻¹ • w n))
    (hh : ∀ n, (w (n + 1)).1 = q • T₁.symm (w n).1 - T₁.symm (c (n + 1)).1)
    (hv : ∀ n, (w n).2 = q⁻¹ • (T₂ (w (n + 1)).2 + (c (n + 1)).2)) :
    ∀ n, g ((q ^ (n + 1))⁻¹ • w (n + 1)) = (q ^ n)⁻¹ • w n := by
  intro n
  have hhor : T₁ (w (n + 1)).1 + (c (n + 1)).1 = q • (w n).1 := by
    rw [hh, map_sub, map_smul, T₁.apply_symm_apply, T₁.apply_symm_apply]
    exact sub_add_cancel _ _
  have hver : T₂ (w (n + 1)).2 + (c (n + 1)).2 = q • (w n).2 := by
    simpa only [smul_smul, mul_inv_cancel₀ hq, one_smul] using
      (congrArg (fun x : E₂ ↦ q • x) (hv n)).symm
  have ht : (T₁ (w (n + 1)).1, T₂ (w (n + 1)).2) + c (n + 1) = q • w n :=
    Prod.ext hhor hver
  have hpow : q ^ (n + 1) ≠ 0 := pow_ne_zero _ hq
  have hscale : (q ^ (n + 1))⁻¹ * q = (q ^ n)⁻¹ := by
    rw [pow_succ]
    field_simp
  calc
    g ((q ^ (n + 1))⁻¹ • w (n + 1)) =
        (q ^ (n + 1))⁻¹ •
          ((T₁ (w (n + 1)).1, T₂ (w (n + 1)).2) + c (n + 1)) := by
      rw [hR, smul_add, hc]
      simp [map_smul, smul_smul, hpow, Prod.smul_mk]
    _ = (q ^ n)⁻¹ • w n := by rw [ht, smul_smul, hscale]

end HolomorphicAnosov.Analysis

