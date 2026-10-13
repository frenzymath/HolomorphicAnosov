import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

namespace HolomorphicAnosov.Analysis.MarkedRectangle
open Set

/-- The real Cayley coordinate increases strictly along the open positive turn.
The real coordinate is -sin(t)/(1-cos(t)); its derivative is
1/(1-cos(t)), positive for 0<t<2pi. -/
theorem cayley_exp_strictMonoOn :
    StrictMonoOn (fun t : ℝ ↦
      (Complex.I * (1 + (Circle.exp t : ℂ)) / (1 - (Circle.exp t : ℂ))).re)
      (Ioo 0 (2 * Real.pi)) := by
  have hden {t : ℝ} (ht : t ∈ Ioo 0 (2 * Real.pi)) : 0 < 1 - Real.cos t := by
    have hne : Real.cos t ≠ 1 := by
      intro he
      have := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos, ht.1]) ht.2).mp he
      linarith [ht.1]
    exact sub_pos.mpr (lt_of_le_of_ne (Real.cos_le_one t) hne)
  have heq {t : ℝ} (ht : t ∈ Ioo 0 (2 * Real.pi)) :
      (Complex.I * (1 + (Circle.exp t : ℂ)) / (1 - (Circle.exp t : ℂ))).re =
        -Real.sin t / (1 - Real.cos t) := by
    simp only [Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
      Complex.div_re, Complex.sub_re, Complex.sub_im, Complex.normSq_apply]
    have hd := (hden ht).ne'
    have hsq := Real.sin_sq_add_cos_sq t
    ring_nf
    have he : 1 - Real.cos t * 2 + Real.cos t ^ 2 + Real.sin t ^ 2 =
        2 * (1-Real.cos t) := by nlinarith [hsq]
    rw [he]
    field_simp [hd]
  have hf : StrictMonoOn (fun t : ℝ ↦ -Real.sin t / (1-Real.cos t))
      (Ioo 0 (2*Real.pi)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    · exact ((Real.continuous_sin.neg).continuousOn.div
        (continuous_const.sub Real.continuous_cos).continuousOn
        (fun t ht ↦ (hden ht).ne'))
    intro t ht
    rw [interior_Ioo] at ht
    have hd := ((Real.hasDerivAt_sin t).neg.div
      ((hasDerivAt_const t (1:ℝ)).sub (Real.hasDerivAt_cos t)) (hden ht).ne').deriv
    change deriv (fun t : ℝ ↦ -Real.sin t / (1-Real.cos t)) t = _ at hd
    rw [hd]
    dsimp
    apply div_pos _ (sq_pos_of_pos (hden ht))
    have hs := Real.sin_sq_add_cos_sq t
    nlinarith [hden ht]
  intro x hx y hy hxy
  dsimp only
  rw [heq hx, heq hy]
  exact hf hx hy hxy

end HolomorphicAnosov.Analysis.MarkedRectangle
