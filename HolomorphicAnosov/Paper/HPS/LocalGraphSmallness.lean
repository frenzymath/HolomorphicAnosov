import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Group.Constructions

open Filter
open scoped Topology _root_.Topology

namespace HolomorphicAnosov

/-- For nonnegative `a`, positive `ρ`, `a < ρ⁻¹`, and `k < ρ`, some positive remainder bound satisfies all strict inequalities needed by the two graph constructions. (HPS, pp. 53–54, 60) -/
theorem hps_local_graph_smallness
    (a k ρ : ℝ) (ha₀ : 0 ≤ a) (hρ : 0 < ρ)
    (ha : a < ρ⁻¹) (hk : k < ρ) :
    ∃ ε : ℝ, 0 < ε ∧ 2 * a * ε < 1 ∧
      a / (1 - a * ε) < ρ⁻¹ ∧ k + ε < ρ ∧
      (a ≠ 0 → a⁻¹ - 2 * ε > ρ) ∧
      (a < 1 → a / (1 - a * ε) < 1) ∧
      (k < 1 → k + ε < 1 ∧ k + 2 * ε < min ρ 1 ∧
        (a ≠ 0 → a⁻¹ - 4 * ε > ρ)) := by
  have ha_inv : a ≠ 0 → ρ < a⁻¹ := by
    intro hne
    exact (lt_inv_comm₀ (lt_of_le_of_ne ha₀ (Ne.symm hne)) hρ).mp ha
  have hmul : ∀ᶠ ε : ℝ in 𝓝 0, 2 * a * ε < 1 := by
    apply ContinuousAt.eventually_lt (by fun_prop) (by fun_prop)
    norm_num
  have hdiv : ∀ᶠ ε : ℝ in 𝓝 0, a / (1 - a * ε) < ρ⁻¹ := by
    apply ContinuousAt.eventually_lt
      (ContinuousAt.div₀ (by fun_prop) (by fun_prop) (by norm_num)) (by fun_prop)
    simpa using ha
  have hkρ : ∀ᶠ ε : ℝ in 𝓝 0, k + ε < ρ := by
    apply ContinuousAt.eventually_lt (by fun_prop) (by fun_prop)
    simpa using hk
  have haρ : ∀ᶠ ε : ℝ in 𝓝 0, a ≠ 0 → ρ < a⁻¹ - 2 * ε := by
    by_cases hne : a = 0
    · filter_upwards with ε
      simp [hne]
    · have hev : ∀ᶠ ε : ℝ in 𝓝 0, ρ < a⁻¹ - 2 * ε := by
        apply ContinuousAt.eventually_lt (by fun_prop) (by fun_prop)
        simpa using ha_inv hne
      filter_upwards [hev] with ε hε _
      exact hε
  have ha1 : ∀ᶠ ε : ℝ in 𝓝 0, a < 1 → a / (1 - a * ε) < 1 := by
    by_cases h : a < 1
    · have hev : ∀ᶠ ε : ℝ in 𝓝 0, a / (1 - a * ε) < 1 := by
        apply ContinuousAt.eventually_lt
          (ContinuousAt.div₀ (by fun_prop) (by fun_prop) (by norm_num)) (by fun_prop)
        simpa using h
      filter_upwards [hev] with ε hε _
      exact hε
    · filter_upwards with ε
      exact fun h' ↦ (h h').elim
  have hk1 : ∀ᶠ ε : ℝ in 𝓝 0, k < 1 →
      k + ε < 1 ∧ k + 2 * ε < min ρ 1 ∧ (a ≠ 0 → ρ < a⁻¹ - 4 * ε) := by
    by_cases h : k < 1
    · have hev₁ : ∀ᶠ ε : ℝ in 𝓝 0, k + ε < 1 := by
        apply ContinuousAt.eventually_lt (by fun_prop) (by fun_prop)
        simpa using h
      have hev₂ : ∀ᶠ ε : ℝ in 𝓝 0, k + 2 * ε < min ρ 1 := by
        apply ContinuousAt.eventually_lt (by fun_prop) (by fun_prop)
        simpa using (lt_min hk h)
      have hev₃ : ∀ᶠ ε : ℝ in 𝓝 0, a ≠ 0 → ρ < a⁻¹ - 4 * ε := by
        by_cases hne : a = 0
        · filter_upwards with ε
          simp [hne]
        · have hev : ∀ᶠ ε : ℝ in 𝓝 0, ρ < a⁻¹ - 4 * ε := by
            apply ContinuousAt.eventually_lt (by fun_prop) (by fun_prop)
            simpa using ha_inv hne
          filter_upwards [hev] with ε hε _
          exact hε
      filter_upwards [hev₁, hev₂, hev₃] with ε hε₁ hε₂ hε₃ _
      exact ⟨hε₁, hε₂, hε₃⟩
    · filter_upwards with ε
      exact fun h' ↦ (h h').elim
  have hev : ∀ᶠ ε : ℝ in 𝓝 0, 2 * a * ε < 1 ∧
      a / (1 - a * ε) < ρ⁻¹ ∧ k + ε < ρ ∧
      (a ≠ 0 → ρ < a⁻¹ - 2 * ε) ∧
      (a < 1 → a / (1 - a * ε) < 1) ∧
      (k < 1 → k + ε < 1 ∧ k + 2 * ε < min ρ 1 ∧
        (a ≠ 0 → ρ < a⁻¹ - 4 * ε)) := by
    filter_upwards [hmul, hdiv, hkρ, haρ, ha1, hk1] with ε h₁ h₂ h₃ h₄ h₅ h₆
    exact ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hev
  obtain ⟨ε, hε₀, hεδ⟩ := exists_between hδ
  refine ⟨ε, hε₀, ?_⟩
  exact hball (by simpa [Real.dist_eq, abs_of_pos hε₀] using hεδ)

end HolomorphicAnosov
