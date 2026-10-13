import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
noncomputable section
namespace HolomorphicAnosov.Analysis.MarkedRectangle
/-- Positive square-root parameter for a strict four-point cross-ratio inequality.
Source: Bak--Newman, *Complex Analysis* (3rd ed.), pp.184--186. -/
theorem canonical_cross_ratio_parameter
    {p q r s : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : 0 < s)
    (hcross : p * s < r * q) :
    ∃ U V k : ℝ, 0 < U ∧ 0 < V ∧ U < V ∧ U ^ 2 = p * s ∧ V ^ 2 = r * q ∧
      k = (V - U) / (V + U) ∧ 0 < k ∧ k < 1 := by
  let U : ℝ := Real.sqrt (p * s)
  let V : ℝ := Real.sqrt (r * q)
  have hps : 0 < p * s := mul_pos hp hs
  have hrq : 0 < r * q := mul_pos hr hq
  have hU : 0 < U := by dsimp [U]; exact Real.sqrt_pos.2 hps
  have hV : 0 < V := by dsimp [V]; exact Real.sqrt_pos.2 hrq
  have hU2 : U ^ 2 = p * s := by dsimp [U]; exact Real.sq_sqrt hps.le
  have hV2 : V ^ 2 = r * q := by dsimp [V]; exact Real.sq_sqrt hrq.le
  have hUV : U < V := by nlinarith [hcross]
  let k : ℝ := (V - U) / (V + U)
  have hden : 0 < V + U := by linarith
  have hk0 : 0 < k := by dsimp [k]; exact div_pos (by linarith) hden
  have hk1 : k < 1 := by dsimp [k]; apply (div_lt_iff₀ hden).2; linarith
  exact ⟨U, V, k, hU, hV, hUV, hU2, hV2, rfl, hk0, hk1⟩
end HolomorphicAnosov.Analysis.MarkedRectangle
