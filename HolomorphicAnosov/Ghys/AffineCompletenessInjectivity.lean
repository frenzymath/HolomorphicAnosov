import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic

namespace HolomorphicAnosov.Ghys

open Filter Topology _root_.Topology


theorem affine_completeness_injective_of_backward_contraction
    {X : Type*} [MetricSpace X] {L : ℕ → Type*} [∀ n, MetricSpace (L n)]
    (D : X → ℂ) (E : (n : ℕ) → L n → ℂ) (B : (n : ℕ) → X → L n)
    (a b : ℕ → ℂ) {C ρ ε : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hε : 0 < ε)
    (hB : ∀ n, Function.Injective (B n))
    (hcontract : ∀ n x y, dist (B n x) (B n y) ≤ C * ρ ^ n * dist x y)
    (ha : ∀ n, a n ≠ 0)
    (htransport : ∀ n x, D x = a n * E n (B n x) + b n)
    (hseparate : ∀ n u v, dist u v < ε → E n u = E n v → u = v) :
    Function.Injective D := by
  intro x y hxy
  have hdecay : Tendsto (fun n : ℕ ↦ C * ρ ^ n * dist x y) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ1).const_mul C).mul_const (dist x y)
  obtain ⟨n, hn⟩ := (hdecay.eventually (eventually_lt_nhds hε)).exists
  apply hB n
  apply hseparate n _ _ (lt_of_le_of_lt (hcontract n x y) hn)
  apply mul_left_cancel₀ (ha n)
  apply add_right_cancel (b := b n)
  rw [← htransport n x, ← htransport n y]
  exact hxy


end HolomorphicAnosov.Ghys
