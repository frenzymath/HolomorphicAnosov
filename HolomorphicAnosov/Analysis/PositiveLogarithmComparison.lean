import HolomorphicAnosov.Analysis.PositiveCircleLogarithmOrder

namespace HolomorphicAnosov.Analysis.MarkedRectangle
open Set

/-- Two positive, injective angular lifts starting at the same direction order
matching interior points in the same way. Normalize the logarithms, subtract
their initial angles, and use exponential injectivity on one open turn. -/
theorem positive_logarithms_order
    (L M : C(Icc (0 : ℝ) 1, ℂ))
    (hL : StrictMono (fun t ↦ (L t).im)) (hM : StrictMono (fun t ↦ (M t).im))
    (hiL : L 1 - L 0 = (2 * Real.pi : ℂ) * Complex.I)
    (hiM : M 1 - M 0 = (2 * Real.pi : ℂ) * Complex.I)
    (hzero : Complex.exp (L 0) = Complex.exp (M 0))
    (t₀ t₁ s₀ s₁ : Icc (0 : ℝ) 1)
    (ht₀ : 0 < t₀ ∧ t₀ < 1) (ht₁ : 0 < t₁ ∧ t₁ < 1)
    (hs₀ : 0 < s₀ ∧ s₀ < 1) (hs₁ : 0 < s₁ ∧ s₁ < 1)
    (he₀ : Complex.exp (L t₀) = Complex.exp (M s₀))
    (he₁ : Complex.exp (L t₁) = Complex.exp (M s₁))
    (hs : s₀ < s₁) : t₀ < t₁ := by
  have inc (F : C(Icc (0 : ℝ) 1, ℂ))
      (hi : F 1 - F 0 = (2 * Real.pi : ℂ) * Complex.I) :
      (F 1).im - (F 0).im = 2 * Real.pi := by
    simpa using congrArg Complex.im hi
  have eqangle (t s : Icc (0 : ℝ) 1)
      (ht : 0 < t ∧ t < 1) (hs : 0 < s ∧ s < 1)
      (he : Complex.exp (L t) = Complex.exp (M s)) :
      (L t).im - (L 0).im = (M s).im - (M 0).im := by
    apply Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by simp)
    · constructor <;> linarith [hL ht.1, hL ht.2, inc L hiL]
    · constructor <;> linarith [hM hs.1, hM hs.2, inc M hiM]
    · apply Subtype.ext
      change Complex.exp (((L t).im - (L 0).im : ℝ) * Complex.I) =
        Complex.exp (((M s).im - (M 0).im : ℝ) * Complex.I)
      push_cast
      rw [sub_mul, sub_mul, Complex.exp_sub, Complex.exp_sub,
        exp_im_eq_normalized, exp_im_eq_normalized,
        exp_im_eq_normalized, exp_im_eq_normalized, he, hzero]
  have h₀ := eqangle t₀ s₀ ht₀ hs₀ he₀
  have h₁ := eqangle t₁ s₁ ht₁ hs₁ he₁
  apply hL.lt_iff_lt.mp
  linarith [hM hs]

end HolomorphicAnosov.Analysis.MarkedRectangle
