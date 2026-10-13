import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.InnerProductSpace.Convex

open scoped ComplexConjugate

namespace HolomorphicAnosov.Analysis

/-- Each strict side of a chord between distinct circle points meets the circle.
Source: Tao, 246C Notes 2, §2 Theorem 20, chord-cap step, with the elementary
round-circle geometry expanded in the collapsed-boundary DAG proof step 7. -/
theorem circle_chord_strict_side_nonempty {ζ ω : Circle} (hne : ζ ≠ ω) :
    {z : Circle | (conj ((ω : ℂ) - ζ) * ((z : ℂ) - ζ)).im < 0}.Nonempty := by
  let d : ℂ := (ω : ℂ) - ζ
  have hd : d ≠ 0 := by
    intro h
    apply hne
    exact (Circle.coe_injective (sub_eq_zero.mp h)).symm
  have hr : 0 < ‖d‖ := norm_pos_iff.mpr hd
  let m : ℂ := (1 / 2 : ℝ) • (ζ : ℂ) + (1 / 2 : ℝ) • (ω : ℂ)
  have hm : ‖m‖ < 1 := by
    exact norm_combo_lt_of_ne (by simp) (by simp)
      (fun h => hne (Circle.coe_injective h)) (by norm_num) (by norm_num) (by norm_num)
  have hoffset : (conj d * m).im = (conj d * (ζ : ℂ)).im := by
    dsimp [d, m]
    simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.add_im]
    ring
  have hbound : |(conj d * (ζ : ℂ)).im| < ‖d‖ := by
    rw [← hoffset]
    calc
      |(conj d * m).im| ≤ ‖conj d * m‖ := Complex.abs_im_le_norm _
      _ = ‖d‖ * ‖m‖ := by simp
      _ < ‖d‖ := by nlinarith
  let z : ℂ := -(Complex.I * d) / (‖d‖ : ℂ)
  have hz : ‖z‖ = 1 := by simp [z, hr.ne']
  refine ⟨⟨z, mem_sphere_zero_iff_norm.mpr hz⟩, ?_⟩
  change (conj d * (z - (ζ : ℂ))).im < 0
  have hdz : conj d * z = -(‖d‖ : ℂ) * Complex.I := by
    dsimp [z]
    rw [← mul_div_assoc]
    have hmul : conj d * -(Complex.I * d) = -(Complex.normSq d : ℂ) * Complex.I := by
      calc
        conj d * -(Complex.I * d) = -(conj d * d) * Complex.I := by ring
        _ = _ := by rw [← Complex.normSq_eq_conj_mul_self]
    rw [hmul, Complex.normSq_eq_norm_sq]
    push_cast
    field_simp
  rw [mul_sub, Complex.sub_im, hdz]
  have hnegim : (-(‖d‖ : ℂ) * Complex.I).im = -‖d‖ := by simp
  rw [hnegim]
  have := (abs_lt.mp hbound).1
  linarith

end HolomorphicAnosov.Analysis

