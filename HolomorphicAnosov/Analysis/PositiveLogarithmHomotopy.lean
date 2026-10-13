import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingHomotopy
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingEqOfIncrement
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

namespace HolomorphicAnosov

/-- Transport a full positive logarithm increment along a homotopy avoiding zero.
This is the logarithm form of homotopy invariance of winding number. -/
theorem positive_logarithm_of_homotopy (γ₀ γ₁ : ComplexLoop)
    (h₀ : ∀ z, γ₀ z ≠ 0) (h₁ : ∀ z, γ₁ z ≠ 0)
    (h : LoopHomotopyAvoids γ₀ γ₁ 0)
    (L : C(↑unitInterval, ℂ))
    (hL : ∀ t, Complex.exp (L t) = γ₀ (Circle.exp (2 * Real.pi * (t : ℝ))))
    (hi : L 1 - L 0 = (2 * Real.pi : ℂ) * Complex.I) :
    ∃ M : C(↑unitInterval, ℂ),
      (∀ t, Complex.exp (M t) = γ₁ (Circle.exp (2 * Real.pi * (t : ℝ)))) ∧
      M 1 - M 0 = (2 * Real.pi : ℂ) * Complex.I := by
  have hw₀ : loopWinding γ₀ 0 h₀ = 1 := by
    apply loopWinding_eq_of_increment γ₀ 0 h₀ L
    · simpa [puncturedLoopPath] using hL
    · simpa using hi
  have hw₁ := (loopWinding_homotopy γ₀ γ₁ 0 h₀ h₁ h).symm.trans hw₀
  obtain ⟨M, hm, hmi⟩ := loopWinding_lift γ₁ 0 h₁
  refine ⟨M, ?_, ?_⟩
  · simpa [puncturedLoopPath] using hm
  · rw [hw₁] at hmi
    simpa [sub_eq_iff_eq_add, add_comm] using hmi

/-- Rotating the starting point of a nonvanishing circle loop preserves its
positive logarithm increment. The rotations through intermediate angles give
an explicit homotopy avoiding zero. -/
theorem positive_logarithm_rotate (γ : ComplexLoop) (hγ : ∀ z, γ z ≠ 0)
    (L : C(↑unitInterval, ℂ))
    (hL : ∀ t, Complex.exp (L t) = γ (Circle.exp (2 * Real.pi * (t : ℝ))))
    (hi : L 1 - L 0 = (2 * Real.pi : ℂ) * Complex.I) (u : Circle) :
    ∃ M : C(↑unitInterval, ℂ),
      (∀ t, Complex.exp (M t) = γ (u * Circle.exp (2 * Real.pi * (t : ℝ)))) ∧
      M 1 - M 0 = (2 * Real.pi : ℂ) * Complex.I := by
  let γ₁ : ComplexLoop := ⟨fun z ↦ γ (u*z), by fun_prop⟩
  apply positive_logarithm_of_homotopy γ γ₁ hγ (fun z ↦ hγ (u*z)) ?_ L hL hi
  refine ⟨⟨fun p ↦ γ (Circle.exp ((p.1 : ℝ) * Complex.arg u) * p.2), by
    fun_prop⟩, ?_, ?_, ?_⟩
  · intro z
    simp
  · intro z
    simp [γ₁]
  · intro t z
    exact hγ _

/-- Subtracting a point strictly inside the unit disk preserves the positive
increment of the circle loop. The straight translation homotopy never meets
zero because each translated center has norm less than one. -/
theorem circle_sub_positive_logarithm (a : ℂ) (ha : ‖a‖ < 1) :
    ∃ M : C(↑unitInterval, ℂ),
      (∀ t, Complex.exp (M t) = (Circle.exp (2 * Real.pi * (t : ℝ)) : ℂ) - a) ∧
      M 1 - M 0 = (2 * Real.pi : ℂ) * Complex.I := by
  let γ₀ : ComplexLoop := ⟨fun z ↦ (z : ℂ), continuous_subtype_val⟩
  let γ₁ : ComplexLoop := ⟨fun z ↦ (z : ℂ)-a, by fun_prop⟩
  have hn (t : unitInterval) (z : Circle) : (z : ℂ) - (t : ℝ) • a ≠ 0 := by
    intro he
    have hh := congrArg norm (sub_eq_zero.mp he)
    rw [Circle.norm_coe, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1] at hh
    have ht := mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg a)
    nlinarith
  refine positive_logarithm_of_homotopy γ₀ γ₁
    (fun z ↦ by
      change (z : ℂ) ≠ 0
      have h := hn 0 z
      change (z : ℂ) - (0 : ℝ) • a ≠ 0 at h
      simp)
    (fun z ↦ by
      change (z : ℂ) - a ≠ 0
      have h := hn 1 z
      change (z : ℂ) - (1 : ℝ) • a ≠ 0 at h
      simpa using h) ?_
    ⟨fun t ↦ (2 * Real.pi * (t : ℝ) : ℂ) * Complex.I, by fun_prop⟩ ?_ ?_
  · refine ⟨⟨fun p ↦ (p.2 : ℂ) - (p.1 : ℝ) • a, by fun_prop⟩, ?_, ?_, ?_⟩
    · intro z; change (z : ℂ) - (0 : ℝ) • a = z; simp
    · intro z; simp [γ₁]
    · exact hn
  · intro t; change Complex.exp _ = (Circle.exp _ : ℂ); simp [Circle.coe_exp]
  · simp

end HolomorphicAnosov
