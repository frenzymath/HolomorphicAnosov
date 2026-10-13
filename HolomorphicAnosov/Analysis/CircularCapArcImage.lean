import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Set Metric
namespace HolomorphicAnosov.Analysis

/-- The explicit circular crosscut parametrizes precisely the part of the circle
inside the unit disk. Source: Conway, Functions of One Complex Variable II,
Chapter 14, Theorem 5.5, p.50, source-disk circular-cap geometry.

After rotation the squared norm is 1+r²+2r cos θ, so disk membership is
cos θ < -r/2. For the reverse inclusion write v=-(z-ζ)/ζ and use its principal
argument. The disk inequality gives |arg v|<arccos(r/2). The affine parameter
(b+arg v)/(2b), where b=arccos(r/2), is strictly between zero and one and
reconstructs z. This proof does not invoke any boundary extension theorem. -/
theorem circular_cap_arc_image (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    (fun t : ℝ ↦ ζ * circleMap 1 r (Real.arccos (-r / 2) +
      (2 * Real.pi - 2 * Real.arccos (-r / 2)) * t)) '' Ioo 0 1 =
      ball (0 : ℂ) 1 ∩ sphere ζ r := by
  let b := Real.arccos (r / 2)
  have hb : 0 < b := Real.arccos_pos.mpr (by linarith)
  have hbπ : b < Real.pi := Real.arccos_lt_pi.mpr (by linarith)
  have ha : Real.arccos (-r / 2) = Real.pi - b := by
    rw [neg_div, Real.arccos_neg]
  have hnorm (u : ℝ) : ‖ζ * circleMap 1 r u‖ ^ 2 =
      1 + r ^ 2 + 2 * r * Real.cos u := by
    rw [norm_mul, hζ, one_mul, Complex.sq_norm]
    simp only [circleMap, Complex.normSq_apply, Complex.add_re, Complex.one_re,
      Complex.mul_re, Complex.ofReal_re, Complex.exp_re, Complex.ofReal_im,
      Complex.exp_im, zero_mul, sub_zero, Complex.add_im, Complex.one_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, zero_add, mul_zero, add_zero,
      mul_one, Real.exp_zero, one_mul]
    nlinarith [Real.sin_sq_add_cos_sq u]
  have hζ0 : ζ ≠ 0 := by intro hz; simp [hz] at hζ
  apply Subset.antisymm
  · rintro z ⟨t, ht, rfl⟩
    let θ := Real.arccos (-r / 2) + (2 * Real.pi - 2 * Real.arccos (-r / 2)) * t
    have ha0 : 0 < Real.arccos (-r / 2) := Real.arccos_pos.mpr (by linarith)
    have haπ : Real.arccos (-r / 2) < Real.pi := Real.arccos_lt_pi.mpr (by linarith)
    have hlo : Real.arccos (-r / 2) < θ := by dsimp [θ]; nlinarith [ht.1]
    have hhi : θ < 2 * Real.pi - Real.arccos (-r / 2) := by dsimp [θ]; nlinarith [ht.2]
    have hc : Real.cos θ < Real.cos (Real.arccos (-r / 2)) := by
      by_cases hmid : θ ≤ Real.pi
      · exact Real.cos_lt_cos_of_nonneg_of_le_pi ha0.le hmid hlo
      · rw [← Real.cos_two_pi_sub θ]
        exact Real.cos_lt_cos_of_nonneg_of_le_pi ha0.le (by linarith) (by linarith)
    rw [Real.cos_arccos (by linarith) (by linarith)] at hc
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_zero_right]
      change ‖ζ * circleMap 1 r θ‖ < 1
      have hh := hnorm θ
      nlinarith [mul_pos hr (sub_pos.mpr hc), norm_nonneg (ζ * circleMap 1 r θ)]
    · rw [mem_sphere, dist_eq_norm]
      have he : ζ * circleMap 1 r θ - ζ = ζ * (circleMap 1 r θ - 1) := by ring
      rw [he, norm_mul, hζ, one_mul, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr]
  · intro z hz
    let v : ℂ := -(z - ζ) / ζ
    have hvnorm : ‖v‖ = r := by
      dsimp [v]
      rw [norm_div, norm_neg, hζ, div_one]
      simpa only [dist_eq_norm] using mem_sphere.mp hz.2
    have hzrep : ζ * circleMap 1 r (Real.pi + v.arg) = z := by
      have hv := Complex.norm_mul_exp_arg_mul_I v
      rw [hvnorm] at hv
      simp only [circleMap, Complex.ofReal_add, add_mul, Complex.exp_add,
        Complex.exp_pi_mul_I]
      calc
        ζ * (1 + (r : ℂ) * (-1 * Complex.exp (v.arg * Complex.I))) =
            ζ - ζ * ((r : ℂ) * Complex.exp (v.arg * Complex.I)) := by ring
        _ = ζ - ζ * v := by rw [hv]
        _ = z := by dsimp [v]; field_simp; ring
    have hcos : r / 2 < Real.cos v.arg := by
      have hn := hnorm (Real.pi + v.arg)
      rw [hzrep, Real.cos_add, Real.cos_pi, Real.sin_pi] at hn
      have hzlt : ‖z‖ < 1 := by simpa using hz.1
      nlinarith [norm_nonneg z]
    have harg : |v.arg| < b := by
      by_contra h
      have hle := Real.cos_le_cos_of_nonneg_of_le_pi (Real.arccos_nonneg (r / 2))
        (Complex.abs_arg_le_pi v) (le_of_not_gt h)
      rw [Real.cos_abs, Real.cos_arccos (by linarith) (by linarith)] at hle
      exact (not_le_of_gt hcos) hle
    rw [abs_lt] at harg
    refine ⟨(b + v.arg) / (2 * b), ⟨?_, ?_⟩, ?_⟩
    · exact div_pos (by linarith) (by positivity)
    · apply (div_lt_one (by positivity : 0 < 2 * b)).mpr
      linarith
    · rw [ha]
      have he : Real.pi - b + (2 * Real.pi - 2 * (Real.pi - b)) *
          ((b + v.arg) / (2 * b)) = Real.pi + v.arg := by
        field_simp [ne_of_gt hb]
        ring
      dsimp
      rw [he]
      exact hzrep

end HolomorphicAnosov.Analysis
