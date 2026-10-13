import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section
open Set _root_.Topology
namespace HolomorphicAnosov

/-! This file establishes a uniform smallness threshold for a compact parameter family. -/
theorem parameter_graph_uniform_threshold
    {ι : Type*} (ρ : ℝ) (A K : ι → ℝ)
    (hρ : 0 < ρ)
    (hA : ∀ i, 0 ≤ A i) (hK : ∀ i, 0 ≤ K i)
    (hAbdd : BddAbove (Set.range A)) (hKbdd : BddAbove (Set.range K))
    (ha : sSup (Set.range A) < ρ⁻¹)
    (hk : sSup (Set.range K) < ρ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ η : ℝ, 0 ≤ η → η < δ →
        ∀ i, A i * η < 1 ∧ A i * (K i + 2 * η) ≤ 1 := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      refine ⟨1, zero_lt_one, ?_⟩
      intro η hη hη1 i
      exact (hι.false i).elim
  | inr hι =>
    have hρinv : 0 < ρ⁻¹ := inv_pos.mpr hρ
    let a₀ : ℝ := sSup (Set.range A)
    let k₀ : ℝ := sSup (Set.range K)
    have hAa : ∀ i, A i ≤ a₀ := by
      intro i
      exact (isLUB_csSup (Set.range_nonempty A) hAbdd).1 ⟨i, rfl⟩
    have hKk : ∀ i, K i ≤ k₀ := by
      intro i
      exact (isLUB_csSup (Set.range_nonempty K) hKbdd).1 ⟨i, rfl⟩
    have ha0 : 0 ≤ a₀ := by
      let i₀ : ι := Classical.choice hι
      exact (hA i₀).trans (hAa i₀)
    have hk0 : 0 ≤ k₀ := by
      let i₀ : ι := Classical.choice hι
      exact (hK i₀).trans (hKk i₀)
    let δ : ℝ := min ((ρ⁻¹ - a₀) / (2 * (a₀ + 1)))
        ((1 - a₀ * k₀) / (2 * (a₀ + 1)))
    have hδ₁ : 0 < (ρ⁻¹ - a₀) / (2 * (a₀ + 1)) := by
      have hnum : 0 < ρ⁻¹ - a₀ := sub_pos.mpr ha
      positivity
    have hδ₂ : 0 < (1 - a₀ * k₀) / (2 * (a₀ + 1)) := by
      have hprod : a₀ * k₀ < 1 := by
        calc
          a₀ * k₀ < ρ⁻¹ * ρ := by gcongr
          _ = 1 := inv_mul_cancel₀ (ne_of_gt hρ)
      have hnum : 0 < 1 - a₀ * k₀ := sub_pos.mpr hprod
      positivity
    refine ⟨δ, lt_min hδ₁ hδ₂, ?_⟩
    intro η hη hηδ i
    have hden : 0 < 2 * (a₀ + 1) := by positivity
    have hη₁ : η < (ρ⁻¹ - a₀) / (2 * (a₀ + 1)) :=
      lt_of_lt_of_le hηδ (min_le_left _ _)
    have hη₂ : η < (1 - a₀ * k₀) / (2 * (a₀ + 1)) :=
      lt_of_lt_of_le hηδ (min_le_right _ _)
    have hηa : 2 * (a₀ + 1) * η < ρ⁻¹ - a₀ := by
      simpa [mul_comm] using (lt_div_iff₀ hden).mp hη₁
    have hηb : 2 * (a₀ + 1) * η < 1 - a₀ * k₀ := by
      simpa [mul_comm] using (lt_div_iff₀ hden).mp hη₂
    have hAη : A i * η ≤ a₀ * η :=
      mul_le_mul_of_nonneg_right (hAa i) hη
    have hAK : A i * (K i + 2 * η) ≤ a₀ * (k₀ + 2 * η) := by
      calc
        A i * (K i + 2 * η) ≤ a₀ * (K i + 2 * η) :=
          mul_le_mul_of_nonneg_right (hAa i)
            (add_nonneg (hK i) (mul_nonneg (by norm_num) hη))
        _ ≤ a₀ * (k₀ + 2 * η) :=
          mul_le_mul_of_nonneg_left
            (by simpa [add_comm] using add_le_add_right (hKk i) (2 * η)) ha0
    constructor
    · have : a₀ * η < 1 := by nlinarith [hηb, mul_nonneg ha0 hk0]
      exact lt_of_le_of_lt hAη this
    · have : a₀ * (k₀ + 2 * η) ≤ 1 := by nlinarith [hηb, ha0, hη]
      exact hAK.trans this


end HolomorphicAnosov
