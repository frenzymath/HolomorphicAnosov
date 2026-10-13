import HolomorphicAnosov.Analysis.Complex.RectangleDividedDifferenceIntegral
import HolomorphicAnosov.Analysis.Complex.RectangleReciprocalKernelNormalization
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Interior rectangle Cauchy-kernel normalization

DAG node: `analysis.rectangle_cauchy_kernel_integral_g9`.
Source: Ahlfors, *Complex Analysis*, 3rd ed. (1979), IV §1.4 Theorem 3,
pp.111–112 and IV §2.1 Lemma 2, pp.116–117; Conway VIII Proposition 1.1,
pp.195–196.
-/

namespace HolomorphicAnosov.Analysis.Complex
open Set
open scoped Interval Topology _root_.Topology

/-- The positively oriented four-side rectangle integral of the Cauchy kernel
has the interior value `2 * π * I * f z`. The rectangle is the closed real/im
product `[[a.re,b.re]] ×ℂ [[a.im,b.im]]`; strict inequalities place `z` in its
interior. The proof is the exceptional-point quotient argument: the divided
difference `(f w-f z)/(w-z)` has zero boundary integral by the existing removable
singularity/rectangle theorem, while the reciprocal kernel has index one by the
published radial-to-circle cancellation and the positive circle Cauchy formula.
All boundary parameter integrals are genuine interval integrals on closed sides.
-/
theorem rectangle_cauchy_kernel_integral
    (U : Set ℂ) (hU : IsOpen U) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U)
    (a b z : ℂ)
    (hR : ([[a.re, b.re]] ×ℂ [[a.im, b.im]]) ⊆ U)
    (har : a.re < z.re) (hrb : z.re < b.re)
    (hai : a.im < z.im) (hib : z.im < b.im) :
    (∫ x : ℝ in a.re..b.re, f (x + a.im * Complex.I) /
      (x + a.im * Complex.I - z)) -
    (∫ x : ℝ in a.re..b.re, f (x + b.im * Complex.I) /
      (x + b.im * Complex.I - z)) +
    Complex.I * (∫ y : ℝ in a.im..b.im, f (b.re + y * Complex.I) /
      (b.re + y * Complex.I - z)) -
    Complex.I * (∫ y : ℝ in a.im..b.im, f (a.re + y * Complex.I) /
      (a.re + y * Complex.I - z)) =
      2 * (Real.pi : ℂ) * Complex.I * f z := by
  /-
  The quotient integral is zero by
  `rectangle_divided_difference_integral_eq_zero`. Subtracting the constant
  `f z` times the reciprocal boundary integral reduces the claim to the
  positive-index normalization of the rectangle. Ahlfors IV §2.1 Lemma 2
  proves that normalization by joining the two rectangle arcs to a positively
  oriented circle and applying the primitive `log` on the two slit-plane
  complements. The Mathlib circle Cauchy theorem supplies the circle integral
  `2 * π * I`; interval-integral subtraction and reversal identify the four
  displayed sides. -/
  have hbottom_ne : ∀ x : ℝ, x + a.im * Complex.I - z ≠ 0 := by
    intro x hx
    have him := congrArg Complex.im (sub_eq_zero.mp hx)
    norm_num at him
    linarith [hai]
  have htop_ne : ∀ x : ℝ, x + b.im * Complex.I - z ≠ 0 := by
    intro x hx
    have him := congrArg Complex.im (sub_eq_zero.mp hx)
    norm_num at him
    linarith [hib]
  have hright_ne : ∀ y : ℝ, b.re + y * Complex.I - z ≠ 0 := by
    intro y hy
    have hre := congrArg Complex.re (sub_eq_zero.mp hy)
    norm_num at hre
    linarith [hrb]
  have hleft_ne : ∀ y : ℝ, a.re + y * Complex.I - z ≠ 0 := by
    intro y hy
    have hre := congrArg Complex.re (sub_eq_zero.mp hy)
    norm_num at hre
    linarith [har]
  have hbottom_map : MapsTo (fun x : ℝ => x + a.im * Complex.I)
      [[a.re, b.re]] ([[a.re, b.re]] ×ℂ [[a.im, b.im]]) := by
    intro x hx
    simp only [Complex.mem_reProdIm]
    constructor
    · simpa using hx
    · simp
  have htop_map : MapsTo (fun x : ℝ => x + b.im * Complex.I)
      [[a.re, b.re]] ([[a.re, b.re]] ×ℂ [[a.im, b.im]]) := by
    intro x hx
    simp only [Complex.mem_reProdIm]
    constructor
    · simpa using hx
    · simp
  have hright_map : MapsTo (fun y : ℝ => b.re + y * Complex.I)
      [[a.im, b.im]] ([[a.re, b.re]] ×ℂ [[a.im, b.im]]) := by
    intro y hy
    simp only [Complex.mem_reProdIm]
    constructor
    · simp
    · simpa using hy
  have hleft_map : MapsTo (fun y : ℝ => a.re + y * Complex.I)
      [[a.im, b.im]] ([[a.re, b.re]] ×ℂ [[a.im, b.im]]) := by
    intro y hy
    simp only [Complex.mem_reProdIm]
    constructor
    · simp
    · simpa using hy
  have hline_bottom : ContinuousOn (fun x : ℝ => x + a.im * Complex.I) [[a.re, b.re]] :=
    ((Complex.continuous_ofReal.comp continuous_id).add continuous_const).continuousOn
  have hline_top : ContinuousOn (fun x : ℝ => x + b.im * Complex.I) [[a.re, b.re]] :=
    ((Complex.continuous_ofReal.comp continuous_id).add continuous_const).continuousOn
  have hline_right : ContinuousOn (fun y : ℝ => b.re + y * Complex.I) [[a.im, b.im]] :=
    (continuous_const.add ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)).continuousOn
  have hline_left : ContinuousOn (fun y : ℝ => a.re + y * Complex.I) [[a.im, b.im]] :=
    (continuous_const.add ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)).continuousOn
  have hbottom_cont : ContinuousOn
      (fun x : ℝ => f (x + a.im * Complex.I) /
        (x + a.im * Complex.I - z)) [[a.re, b.re]] := by
    have hnum := (hf.continuousOn.mono hR).comp hline_bottom hbottom_map
    apply hnum.div (by fun_prop)
    intro x hx
    exact hbottom_ne x
  have htop_cont : ContinuousOn
      (fun x : ℝ => f (x + b.im * Complex.I) /
        (x + b.im * Complex.I - z)) [[a.re, b.re]] := by
    have hnum := (hf.continuousOn.mono hR).comp hline_top htop_map
    apply hnum.div (by fun_prop)
    intro x hx
    exact htop_ne x
  have hright_cont : ContinuousOn
      (fun y : ℝ => f (b.re + y * Complex.I) /
        (b.re + y * Complex.I - z)) [[a.im, b.im]] := by
    have hnum := (hf.continuousOn.mono hR).comp hline_right hright_map
    apply hnum.div (by fun_prop)
    intro y hy
    exact hright_ne y
  have hleft_cont : ContinuousOn
      (fun y : ℝ => f (a.re + y * Complex.I) /
        (a.re + y * Complex.I - z)) [[a.im, b.im]] := by
    have hnum := (hf.continuousOn.mono hR).comp hline_left hleft_map
    apply hnum.div (by fun_prop)
    intro y hy
    exact hleft_ne y
  have hbottom_rec_cont : ContinuousOn
      (fun x : ℝ => 1 / (x + a.im * Complex.I - z)) [[a.re, b.re]] := by
    apply (continuousOn_const.div (by fun_prop) ?_)
    intro x hx
    exact hbottom_ne x
  have htop_rec_cont : ContinuousOn
      (fun x : ℝ => 1 / (x + b.im * Complex.I - z)) [[a.re, b.re]] := by
    apply (continuousOn_const.div (by fun_prop) ?_)
    intro x hx
    exact htop_ne x
  have hright_rec_cont : ContinuousOn
      (fun y : ℝ => 1 / (b.re + y * Complex.I - z)) [[a.im, b.im]] := by
    apply (continuousOn_const.div (by fun_prop) ?_)
    intro y hy
    exact hright_ne y
  have hleft_rec_cont : ContinuousOn
      (fun y : ℝ => 1 / (a.re + y * Complex.I - z)) [[a.im, b.im]] := by
    apply (continuousOn_const.div (by fun_prop) ?_)
    intro y hy
    exact hleft_ne y
  have hbottom_int : IntervalIntegrable
      (fun x : ℝ => f (x + a.im * Complex.I) /
        (x + a.im * Complex.I - z)) MeasureTheory.MeasureSpace.volume a.re b.re :=
    hbottom_cont.intervalIntegrable
  have htop_int : IntervalIntegrable
      (fun x : ℝ => f (x + b.im * Complex.I) /
        (x + b.im * Complex.I - z)) MeasureTheory.MeasureSpace.volume a.re b.re :=
    htop_cont.intervalIntegrable
  have hright_int : IntervalIntegrable
      (fun y : ℝ => f (b.re + y * Complex.I) /
        (b.re + y * Complex.I - z)) MeasureTheory.MeasureSpace.volume a.im b.im :=
    hright_cont.intervalIntegrable
  have hleft_int : IntervalIntegrable
      (fun y : ℝ => f (a.re + y * Complex.I) /
        (a.re + y * Complex.I - z)) MeasureTheory.MeasureSpace.volume a.im b.im :=
    hleft_cont.intervalIntegrable
  have hbottom_rec_int : IntervalIntegrable
      (fun x : ℝ => 1 / (x + a.im * Complex.I - z)) MeasureTheory.MeasureSpace.volume a.re b.re :=
    hbottom_rec_cont.intervalIntegrable
  have htop_rec_int : IntervalIntegrable
      (fun x : ℝ => 1 / (x + b.im * Complex.I - z)) MeasureTheory.MeasureSpace.volume a.re b.re :=
    htop_rec_cont.intervalIntegrable
  have hright_rec_int : IntervalIntegrable
      (fun y : ℝ => 1 / (b.re + y * Complex.I - z)) MeasureTheory.MeasureSpace.volume a.im b.im :=
    hright_rec_cont.intervalIntegrable
  have hleft_rec_int : IntervalIntegrable
      (fun y : ℝ => 1 / (a.re + y * Complex.I - z)) MeasureTheory.MeasureSpace.volume a.im b.im :=
    hleft_rec_cont.intervalIntegrable
  have hbottom_sub :
      (∫ x : ℝ in a.re..b.re, (f (x + a.im * Complex.I) - f z) /
          (x + a.im * Complex.I - z)) =
        (∫ x : ℝ in a.re..b.re, f (x + a.im * Complex.I) /
          (x + a.im * Complex.I - z)) -
          f z * (∫ x : ℝ in a.re..b.re, 1 /
            (x + a.im * Complex.I - z)) := by
    calc
      (∫ x : ℝ in a.re..b.re, (f (x + a.im * Complex.I) - f z) /
          (x + a.im * Complex.I - z)) =
          ∫ x : ℝ in a.re..b.re, f (x + a.im * Complex.I) /
            (x + a.im * Complex.I - z) - f z *
              (1 / (x + a.im * Complex.I - z)) := by
        apply intervalIntegral.integral_congr
        intro x hx
        field_simp [hbottom_ne x]
      _ = (∫ x : ℝ in a.re..b.re, f (x + a.im * Complex.I) /
            (x + a.im * Complex.I - z)) -
          ∫ x : ℝ in a.re..b.re, f z *
            (1 / (x + a.im * Complex.I - z)) :=
        intervalIntegral.integral_sub hbottom_int (hbottom_rec_int.const_mul (f z))
      _ = (∫ x : ℝ in a.re..b.re, f (x + a.im * Complex.I) /
            (x + a.im * Complex.I - z)) - f z *
          (∫ x : ℝ in a.re..b.re, 1 /
            (x + a.im * Complex.I - z)) := by
        rw [intervalIntegral.integral_const_mul]
  have htop_sub :
      (∫ x : ℝ in a.re..b.re, (f (x + b.im * Complex.I) - f z) /
          (x + b.im * Complex.I - z)) =
        (∫ x : ℝ in a.re..b.re, f (x + b.im * Complex.I) /
          (x + b.im * Complex.I - z)) -
          f z * (∫ x : ℝ in a.re..b.re, 1 /
            (x + b.im * Complex.I - z)) := by
    calc
      (∫ x : ℝ in a.re..b.re, (f (x + b.im * Complex.I) - f z) /
          (x + b.im * Complex.I - z)) =
          ∫ x : ℝ in a.re..b.re, f (x + b.im * Complex.I) /
            (x + b.im * Complex.I - z) - f z *
              (1 / (x + b.im * Complex.I - z)) := by
        apply intervalIntegral.integral_congr
        intro x hx
        field_simp [htop_ne x]
      _ = (∫ x : ℝ in a.re..b.re, f (x + b.im * Complex.I) /
            (x + b.im * Complex.I - z)) -
          ∫ x : ℝ in a.re..b.re, f z *
            (1 / (x + b.im * Complex.I - z)) :=
        intervalIntegral.integral_sub htop_int (htop_rec_int.const_mul (f z))
      _ = (∫ x : ℝ in a.re..b.re, f (x + b.im * Complex.I) /
            (x + b.im * Complex.I - z)) - f z *
          (∫ x : ℝ in a.re..b.re, 1 /
            (x + b.im * Complex.I - z)) := by
        rw [intervalIntegral.integral_const_mul]
  have hright_sub :
      (∫ y : ℝ in a.im..b.im, (f (b.re + y * Complex.I) - f z) /
          (b.re + y * Complex.I - z)) =
        (∫ y : ℝ in a.im..b.im, f (b.re + y * Complex.I) /
          (b.re + y * Complex.I - z)) -
          f z * (∫ y : ℝ in a.im..b.im, 1 /
            (b.re + y * Complex.I - z)) := by
    calc
      (∫ y : ℝ in a.im..b.im, (f (b.re + y * Complex.I) - f z) /
          (b.re + y * Complex.I - z)) =
          ∫ y : ℝ in a.im..b.im, f (b.re + y * Complex.I) /
            (b.re + y * Complex.I - z) - f z *
              (1 / (b.re + y * Complex.I - z)) := by
        apply intervalIntegral.integral_congr
        intro y hy
        field_simp [hright_ne y]
      _ = (∫ y : ℝ in a.im..b.im, f (b.re + y * Complex.I) /
            (b.re + y * Complex.I - z)) -
          ∫ y : ℝ in a.im..b.im, f z *
            (1 / (b.re + y * Complex.I - z)) :=
        intervalIntegral.integral_sub hright_int (hright_rec_int.const_mul (f z))
      _ = (∫ y : ℝ in a.im..b.im, f (b.re + y * Complex.I) /
            (b.re + y * Complex.I - z)) - f z *
          (∫ y : ℝ in a.im..b.im, 1 /
            (b.re + y * Complex.I - z)) := by
        rw [intervalIntegral.integral_const_mul]
  have hleft_sub :
      (∫ y : ℝ in a.im..b.im, (f (a.re + y * Complex.I) - f z) /
          (a.re + y * Complex.I - z)) =
        (∫ y : ℝ in a.im..b.im, f (a.re + y * Complex.I) /
          (a.re + y * Complex.I - z)) -
          f z * (∫ y : ℝ in a.im..b.im, 1 /
            (a.re + y * Complex.I - z)) := by
    calc
      (∫ y : ℝ in a.im..b.im, (f (a.re + y * Complex.I) - f z) /
          (a.re + y * Complex.I - z)) =
          ∫ y : ℝ in a.im..b.im, f (a.re + y * Complex.I) /
            (a.re + y * Complex.I - z) - f z *
              (1 / (a.re + y * Complex.I - z)) := by
        apply intervalIntegral.integral_congr
        intro y hy
        field_simp [hleft_ne y]
      _ = (∫ y : ℝ in a.im..b.im, f (a.re + y * Complex.I) /
            (a.re + y * Complex.I - z)) -
          ∫ y : ℝ in a.im..b.im, f z *
            (1 / (a.re + y * Complex.I - z)) :=
        intervalIntegral.integral_sub hleft_int (hleft_rec_int.const_mul (f z))
      _ = (∫ y : ℝ in a.im..b.im, f (a.re + y * Complex.I) /
            (a.re + y * Complex.I - z)) - f z *
          (∫ y : ℝ in a.im..b.im, 1 /
            (a.re + y * Complex.I - z)) := by
        rw [intervalIntegral.integral_const_mul]
  have hdiv := rectangle_divided_difference_integral_eq_zero
    U hU f hf a b z hR har hrb hai hib
  have hrec := rectangle_reciprocal_kernel_normalization a b z har hrb hai hib
  rw [hbottom_sub, htop_sub, hright_sub, hleft_sub] at hdiv
  linear_combination hdiv + f z * hrec

end HolomorphicAnosov.Analysis.Complex
