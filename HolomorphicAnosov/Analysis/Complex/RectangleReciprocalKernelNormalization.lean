import HolomorphicAnosov.Analysis.Complex.RectangleReciprocalKernelCertificate

/-!
# Reciprocal kernel normalization on an interior rectangle

Source: Ahlfors, *Complex Analysis*, 3rd ed. (1979), IV §2.1 Lemma 2,
pp.116–117.  The positively oriented boundary of a rectangle has integral
`2 * π * I` for the reciprocal kernel centered at any strict interior point.
The published proof joins the two rectangle arcs to a positively oriented
circle by radial segments, applies the logarithm primitive on the two slit
plane complements to cancel the auxiliary curves, and uses the circle Cauchy
formula for the remaining circle.  This exact interval-integral normalization
is isolated here because Mathlib's rectangle Cauchy theorem only treats
continuous integrands on the closed rectangle and does not package the
interior-pole index calculation.
-/

namespace HolomorphicAnosov.Analysis.Complex

open Set
open scoped Interval Topology _root_.Topology

theorem rectangle_reciprocal_side_integrable
    (a b z : ℂ)
    (har : a.re < z.re) (hrb : z.re < b.re)
    (hai : a.im < z.im) (hib : z.im < b.im) :
    IntervalIntegrable (fun x : ℝ => 1 / (x + a.im * Complex.I - z)) MeasureTheory.MeasureSpace.volume a.re b.re ∧
    IntervalIntegrable (fun x : ℝ => 1 / (x + b.im * Complex.I - z)) MeasureTheory.MeasureSpace.volume a.re b.re ∧
    IntervalIntegrable (fun y : ℝ => 1 / (b.re + y * Complex.I - z)) MeasureTheory.MeasureSpace.volume a.im b.im ∧
    IntervalIntegrable (fun y : ℝ => 1 / (a.re + y * Complex.I - z)) MeasureTheory.MeasureSpace.volume a.im b.im := by
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
  have hb : ContinuousOn (fun x : ℝ => 1 / (x + a.im * Complex.I - z)) [[a.re, b.re]] := by
    apply (continuousOn_const.div (by fun_prop) ?_)
    intro x hx; exact hbottom_ne x
  have ht : ContinuousOn (fun x : ℝ => 1 / (x + b.im * Complex.I - z)) [[a.re, b.re]] := by
    apply (continuousOn_const.div (by fun_prop) ?_)
    intro x hx; exact htop_ne x
  have hr : ContinuousOn (fun y : ℝ => 1 / (b.re + y * Complex.I - z)) [[a.im, b.im]] := by
    apply (continuousOn_const.div (by fun_prop) ?_)
    intro y hy; exact hright_ne y
  have hl : ContinuousOn (fun y : ℝ => 1 / (a.re + y * Complex.I - z)) [[a.im, b.im]] := by
    apply (continuousOn_const.div (by fun_prop) ?_)
    intro y hy; exact hleft_ne y
  exact ⟨hb.intervalIntegrable, ht.intervalIntegrable, hr.intervalIntegrable, hl.intervalIntegrable⟩

/-- The reciprocal kernel has positive index one around a strict interior rectangle. -/
theorem rectangle_reciprocal_kernel_normalization
    (a b z : ℂ)
    (har : a.re < z.re) (hrb : z.re < b.re)
    (hai : a.im < z.im) (hib : z.im < b.im) :
    (∫ x : ℝ in a.re..b.re, 1 / (x + a.im * Complex.I - z)) -
    (∫ x : ℝ in a.re..b.re, 1 / (x + b.im * Complex.I - z)) +
    Complex.I * (∫ y : ℝ in a.im..b.im, 1 / (b.re + y * Complex.I - z)) -
    Complex.I * (∫ y : ℝ in a.im..b.im, 1 / (a.re + y * Complex.I - z)) =
      2 * (Real.pi : ℂ) * Complex.I := by
  exact (rectangle_reciprocal_kernel_certificate a b z har hrb hai hib
    (rectangle_reciprocal_side_integrable a b z har hrb hai hib)).identity

end HolomorphicAnosov.Analysis.Complex
