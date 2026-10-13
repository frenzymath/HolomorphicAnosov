import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingLift

namespace HolomorphicAnosov


/-- A continuous nonvanishing odd loop has nonzero winding about zero.

Agent-written proof: lift its once-around parametrization to an exponential
logarithm L on [0,1]. The exponential of L((t+1)/2)-L(t/2) is constantly -1,
by oddness. Uniqueness of lifts makes this difference constant. At t=0 and t=1
this says the two half-turn increments agree. If total winding were zero, their
sum would be zero, so both would be zero. Their exponential would then be 1,
contradicting -1. Nonvanishing is essential, and no differentiability or injectivity
of the loop is used. -/
theorem loopWinding_ne_zero_of_odd (γ : ComplexLoop)
    (hne : ∀ z, γ z ≠ 0) (hodd : ∀ z, γ (-z) = -γ z) :
    loopWinding γ 0 hne ≠ 0 := by
  obtain ⟨L, hL, hperiod⟩ := loopWinding_lift γ 0 hne
  let a (t : unitInterval) : unitInterval := ⟨(t : ℝ) / 2, by
    constructor <;> nlinarith [t.property.1, t.property.2]⟩
  let b (t : unitInterval) : unitInterval := ⟨((t : ℝ) + 1) / 2, by
    constructor <;> nlinarith [t.property.1, t.property.2]⟩
  have hshift (t : unitInterval) :
      Circle.exp (2 * Real.pi * (b t : ℝ)) = -Circle.exp (2 * Real.pi * (a t : ℝ)) := by
    apply Subtype.ext
    simp only [Circle.coe_exp, Circle.coe_neg]
    have he : (↑(2 * Real.pi * ((↑t + 1) / 2)) : ℂ) * Complex.I =
        (↑(2 * Real.pi * ((↑t : ℝ) / 2)) : ℂ) * Complex.I + Real.pi * Complex.I := by
      push_cast
      ring
    change Complex.exp ((↑(2 * Real.pi * ((↑t + 1) / 2)) : ℂ) * Complex.I) = _
    rw [he, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have hcont : Continuous (fun t ↦ L (b t) - L (a t)) := by
    apply Continuous.sub
    · exact L.continuous.comp (by fun_prop)
    · exact L.continuous.comp (by fun_prop)
  have hexp (t : unitInterval) : Complex.exp (L (b t) - L (a t)) = -1 := by
    rw [Complex.exp_sub, hL, hL]
    change (γ (Circle.exp (2 * Real.pi * (b t : ℝ))) - 0) /
      (γ (Circle.exp (2 * Real.pi * (a t : ℝ))) - 0) = -1
    rw [hshift, hodd]
    simp [hne]
  have heq := Complex.isCoveringMap_exp.const_of_comp hcont
    (fun t s ↦ show
      (⟨Complex.exp (L (b t) - L (a t)), Complex.exp_ne_zero _⟩ : {z : ℂ // z ≠ 0}) =
      ⟨Complex.exp (L (b s) - L (a s)), Complex.exp_ne_zero _⟩ from
      Subtype.ext ((hexp t).trans (hexp s).symm)) (0 : unitInterval) 1
  have ha0 : a 0 = 0 := Subtype.ext (by simp [a])
  have hb1 : b 1 = 1 := Subtype.ext (by norm_num [b])
  have hmiddle : b 0 = a 1 := Subtype.ext (by norm_num [a, b])
  rw [ha0, hb1, hmiddle] at heq
  intro hw
  rw [hw, Int.cast_zero, zero_mul, add_zero] at hperiod
  have hhalf : L (a 1) - L 0 = 0 := by
    rw [hperiod] at heq
    linear_combination (1 / 2 : ℂ) * heq
  have hbad := hexp 0
  rw [ha0, hmiddle, hhalf, Complex.exp_zero] at hbad
  norm_num at hbad

end HolomorphicAnosov
