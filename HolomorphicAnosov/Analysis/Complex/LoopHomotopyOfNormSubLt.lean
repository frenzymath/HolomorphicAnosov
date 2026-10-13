import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.Definitions
import Mathlib.Tactic.FunProp

/-!
# Straight interpolation of close loops avoids a marked point

Source: McMullen, *Complex Analysis*, Corollary 1.23, p.12, the straight-line
homotopy in the proof of Rouché's theorem.
-/

open scoped Topology _root_.Topology
namespace HolomorphicAnosov

/-- The straight interpolation between two loops avoids `b` when its displacement
is pointwise smaller than the first loop's distance from `b`.

Source: McMullen, *Complex Analysis*, Corollary 1.23, p.12.
Proof: use `H(t,z) = γ₀(z) + t(γ₁(z)-γ₀(z))`. If it equals `b`, the norm of
`γ₀(z)-b` equals the norm of the interpolation displacement. Since `0 ≤ t ≤ 1`,
that norm is at most `‖γ₁(z)-γ₀(z)‖`, contradicting the strict hypothesis.
The displayed formula is continuous and has the required endpoint values. -/
theorem loopHomotopyAvoids_of_norm_sub_lt (γ₀ γ₁ : ComplexLoop) (b : ℂ)
    (h : ∀ z, ‖γ₁ z - γ₀ z‖ < ‖γ₀ z - b‖) : LoopHomotopyAvoids γ₀ γ₁ b := by
  let H : C(↑unitInterval × Circle, ℂ) :=
    ⟨fun p ↦ γ₀ p.2 + (p.1.val : ℂ) * (γ₁ p.2 - γ₀ p.2), by fun_prop⟩
  refine ⟨H, ?_, ?_, ?_⟩
  · intro z
    simp [H]
  · intro z
    simp [H]
  · intro t z heq
    have he : γ₀ z - b = -((t.val : ℂ) * (γ₁ z - γ₀ z)) := by
      change γ₀ z + (t.val : ℂ) * (γ₁ z - γ₀ z) = b at heq
      rw [← heq, sub_add_eq_sub_sub, sub_self, zero_sub]
    have hbound : ‖γ₀ z - b‖ ≤ ‖γ₁ z - γ₀ z‖ := by
      rw [he, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg t.property.1]
      exact mul_le_of_le_one_left (norm_nonneg _) t.property.2
    exact (not_lt_of_ge hbound) (h z)

end HolomorphicAnosov
