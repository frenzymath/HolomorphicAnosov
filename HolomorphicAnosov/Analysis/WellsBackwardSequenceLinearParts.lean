import HolomorphicAnosov.Analysis.WellsC0SequenceShifts
import HolomorphicAnosov.Analysis.C0DiagonalOperator
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped ZeroAtInfty

namespace HolomorphicAnosov.Analysis

/-- Linear and forcing parts of Wells's backward sequence equation, pp.289–290.
DAG node: `analysis.wells_backward_sequence_linear_parts_g18`.
Lift the horizontal inverse block and the vertical block coordinatewise, compose
with the two null-sequence shifts, and scale by q and its inverse. Erasing the
zeroth forcing coordinate in the horizontal block makes both maps complementary
to the horizontal zeroth-coordinate injection. The product supremum norm gives
the displayed maximum estimate coordinatewise. -/
theorem wells_backward_sequence_linear_parts
    {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    (U : E₁ →L[ℝ] E₁) (V : E₂ →L[ℝ] E₂) (q : ℝ) (hq : 0 < q) :
    ∃ A B : C₀(ℕ, E₁ × E₂) →L[ℝ] C₀(ℕ, E₁ × E₂),
      (∀ w v, (A w + B v) 0 = (0, q⁻¹ • (V (w 1).2 + (v 1).2))) ∧
      (∀ w v n, (A w + B v) (n + 1) =
        (q • U (w n).1 - U (v (n + 1)).1,
          q⁻¹ • (V (w (n + 2)).2 + (v (n + 2)).2))) ∧
      (∀ w v, ‖A w + B v‖ ≤
        max (‖U‖ * (q * ‖w‖ + ‖v‖)) (q⁻¹ * (‖V‖ * ‖w‖ + ‖v‖))) := by
  obtain ⟨S, T, hS0, hS, hT, _, _⟩ := wells_c0_sequence_shifts (E := E₁ × E₂)
  let L₁ : (E₁ × E₂) →L[ℝ] (E₁ × E₂) :=
    (U.comp (ContinuousLinearMap.fst ℝ E₁ E₂)).prod 0
  let L₂ : (E₁ × E₂) →L[ℝ] (E₁ × E₂) :=
    (0 : (E₁ × E₂) →L[ℝ] E₁).prod (V.comp (ContinuousLinearMap.snd ℝ E₁ E₂))
  let P₂ : (E₁ × E₂) →L[ℝ] (E₁ × E₂) :=
    (0 : (E₁ × E₂) →L[ℝ] E₁).prod (ContinuousLinearMap.snd ℝ E₁ E₂)
  let D (L : (E₁ × E₂) →L[ℝ] (E₁ × E₂)) :=
    c0DiagonalOperator (BoundedContinuousFunction.const ℕ L)
  have hD (L : (E₁ × E₂) →L[ℝ] (E₁ × E₂)) (w : C₀(ℕ, E₁ × E₂)) (n : ℕ) :
      D L w n = L (w n) := rfl
  let A := q • (D L₁).comp S + q⁻¹ • (D L₂).comp T
  let B := -(D L₁).comp (S.comp T) + q⁻¹ • (D P₂).comp T
  have hz (w v : C₀(ℕ, E₁ × E₂)) :
      (A w + B v) 0 = (0, q⁻¹ • (V (w 1).2 + (v 1).2)) := by
    simp [A, B, hD, hS0, hT, L₁, L₂, P₂, smul_add]
  have hn (w v : C₀(ℕ, E₁ × E₂)) (n : ℕ) :
      (A w + B v) (n + 1) =
        (q • U (w n).1 - U (v (n + 1)).1,
          q⁻¹ • (V (w (n + 2)).2 + (v (n + 2)).2)) := by
    simp [A, B, hD, hS, hT, L₁, L₂, P₂, smul_add, sub_eq_add_neg, Nat.add_assoc]
  refine ⟨A, B, hz, hn, ?_⟩
  intro w v
  have hc (z : C₀(ℕ, E₁ × E₂)) (n : ℕ) : ‖z n‖ ≤ ‖z‖ :=
    BoundedContinuousFunction.norm_coe_le_norm z.toBCF n
  have hu (z : C₀(ℕ, E₁ × E₂)) (n : ℕ) : ‖U (z n).1‖ ≤ ‖U‖ * ‖z‖ :=
    (U.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      ((norm_fst_le (z n)).trans (hc z n)) (norm_nonneg U))
  have hv (n : ℕ) : ‖q⁻¹ • (V (w n).2 + (v n).2)‖ ≤
      q⁻¹ * (‖V‖ * ‖w‖ + ‖v‖) := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hq.le)]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hq.le)
    exact (norm_add_le _ _).trans (add_le_add
      ((V.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        ((norm_snd_le (w n)).trans (hc w n)) (norm_nonneg V)))
      ((norm_snd_le (v n)).trans (hc v n)))
  have hh (n : ℕ) : ‖q • U (w n).1 - U (v (n + 1)).1‖ ≤
      ‖U‖ * (q * ‖w‖ + ‖v‖) := by
    calc
      _ ≤ ‖q • U (w n).1‖ + ‖U (v (n + 1)).1‖ := norm_sub_le _ _
      _ = q * ‖U (w n).1‖ + ‖U (v (n + 1)).1‖ := by
        rw [norm_smul, Real.norm_of_nonneg hq.le]
      _ ≤ q * (‖U‖ * ‖w‖) + ‖U‖ * ‖v‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (hu w n) hq.le) (hu v (n + 1))
      _ = _ := by ring
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro n
  cases n with
  | zero =>
    change ‖(A w + B v) 0‖ ≤ _
    rw [hz, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
    exact (hv 1).trans (le_max_right _ _)
  | succ n =>
    change ‖(A w + B v) (n + 1)‖ ≤ _
    rw [hn, Prod.norm_def]
    exact max_le_max (hh n) (hv (n + 2))

end HolomorphicAnosov.Analysis

