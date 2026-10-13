import Mathlib.Analysis.Normed.Operator.Basic

namespace HolomorphicAnosov.Analysis

/-- Wells's Case 2 component equations (p.291), DAG node
`analysis.wells_forward_weighted_recurrence_g18`, imply the forward physical
recurrence. If cₙ=q⁻ⁿR(qⁿwₙ), the horizontal and vertical equations combine to
T(wₙ)+cₙ=q wₙ₊₁. Undoing the weights gives g(qⁿwₙ)=qⁿ⁺¹wₙ₊₁. -/
theorem wells_forward_weighted_recurrence
    {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    (T₁ : E₁ ≃L[ℝ] E₁) (T₂ : E₂ →L[ℝ] E₂)
    (q : ℝ) (hq : q ≠ 0) (g R : (E₁ × E₂) → (E₁ × E₂))
    (hR : ∀ z, g z = (T₁ z.1, T₂ z.2) + R z)
    (w c : ℕ → E₁ × E₂)
    (hc : ∀ n, c n = (q ^ n)⁻¹ • R ((q ^ n) • w n))
    (h0 : (w 0).1 = q • T₁.symm (w 1).1 - T₁.symm (c 0).1)
    (hh : ∀ n, (w (n + 1)).1 = q • T₁.symm (w (n + 2)).1 - T₁.symm (c (n + 1)).1)
    (hv : ∀ n, (w (n + 1)).2 = q⁻¹ • (T₂ (w n).2 + (c n).2)) :
    ∀ n, g ((q ^ n) • w n) = (q ^ (n + 1)) • w (n + 1) := by
  intro n
  have hhor : T₁ (w n).1 + (c n).1 = q • (w (n + 1)).1 := by
    cases n with
    | zero =>
      rw [h0, map_sub, map_smul, T₁.apply_symm_apply, T₁.apply_symm_apply]
      exact sub_add_cancel _ _
    | succ n =>
      rw [hh n, map_sub, map_smul, T₁.apply_symm_apply, T₁.apply_symm_apply]
      simp [Nat.add_assoc]
  have hver : T₂ (w n).2 + (c n).2 = q • (w (n + 1)).2 := by
    simpa only [smul_smul, mul_inv_cancel₀ hq, one_smul] using
      (congrArg (fun x : E₂ ↦ q • x) (hv n)).symm
  have ht : (T₁ (w n).1, T₂ (w n).2) + c n =
      q • w (n + 1) := by
    exact Prod.ext hhor hver
  have hpow : q ^ n ≠ 0 := pow_ne_zero _ hq
  calc
    g ((q ^ n) • w n) = (q ^ n) •
        ((T₁ (w n).1, T₂ (w n).2) + c n) := by
      rw [hR, smul_add, hc]
      simp [map_smul, smul_smul, hpow, Prod.smul_mk]
    _ = (q ^ (n + 1)) • w (n + 1) := by rw [ht, smul_smul, pow_succ]

end HolomorphicAnosov.Analysis

