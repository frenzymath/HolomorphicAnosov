import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

namespace HolomorphicAnosov.Analysis.Complex

open Set
open scoped Interval Topology _root_.Topology

structure RectangleReciprocalKernelCertificate (a b z : ℂ) where
  identity :
    (∫ x : ℝ in a.re..b.re, 1 / (x + a.im * Complex.I - z)) -
    (∫ x : ℝ in a.re..b.re, 1 / (x + b.im * Complex.I - z)) +
    Complex.I * (∫ y : ℝ in a.im..b.im, 1 / (b.re + y * Complex.I - z)) -
    Complex.I * (∫ y : ℝ in a.im..b.im, 1 / (a.re + y * Complex.I - z)) =
      2 * (Real.pi : ℂ) * Complex.I

/--
Source: Ahlfors, Complex Analysis 3rd ed. IV §2.1 Lemma 2 pp.116–117.
Proof: Translate each boundary coordinate by z. Along the bottom and top,
the imaginary part is respectively negative and positive, so the principal
logarithm differentiates to the reciprocal kernel. Along the right side the
real part is positive, giving the same primitive. On the left side use log(-w):
its argument has positive real part and its derivative is again 1/w. The
fundamental theorem of calculus evaluates the four oriented side integrals.
At the upper left corner, log(-w) = log(w) - πi; at the lower left corner,
log(-w) = log(w) + πi. Substituting these identities cancels all endpoint
logarithms and leaves 2πi. This is the logarithm-branch computation of the
positive rectangle index, with the supplied side integrability hypotheses.
-/
theorem rectangle_reciprocal_kernel_certificate
    (a b z : ℂ)
    (har : a.re < z.re) (hrb : z.re < b.re)
    (hai : a.im < z.im) (hib : z.im < b.im)
    (_hs : IntervalIntegrable (fun x : ℝ => 1 / (x + a.im * Complex.I - z)) MeasureTheory.MeasureSpace.volume a.re b.re ∧
      IntervalIntegrable (fun x : ℝ => 1 / (x + b.im * Complex.I - z)) MeasureTheory.MeasureSpace.volume a.re b.re ∧
      IntervalIntegrable (fun y : ℝ => 1 / (b.re + y * Complex.I - z)) MeasureTheory.MeasureSpace.volume a.im b.im ∧
      IntervalIntegrable (fun y : ℝ => 1 / (a.re + y * Complex.I - z)) MeasureTheory.MeasureSpace.volume a.im b.im) :
    RectangleReciprocalKernelCertificate a b z := by
  have hcast (x : ℝ) : HasDerivAt (fun t : ℝ ↦ (t : ℂ)) 1 x := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using!
      (Complex.ofRealCLM.hasDerivAt (x := x))
  have hhorizontal (c : ℝ) (hc : c ≠ z.im)
      (hint : IntervalIntegrable (fun x : ℝ ↦ 1 / (x + c * Complex.I - z))
        MeasureTheory.volume a.re b.re) :
      (∫ x : ℝ in a.re..b.re, 1 / (x + c * Complex.I - z)) =
        Complex.log (b.re + c * Complex.I - z) -
          Complex.log (a.re + c * Complex.I - z) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x : ℝ ↦ Complex.log (x + c * Complex.I - z)) _ hint
    intro x hx
    have hslit : (x : ℂ) + c * Complex.I - z ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      right
      simpa using sub_ne_zero.mpr hc
    simpa using (((hcast x).add_const (c * Complex.I)).sub_const z).clog_real hslit
  have hbottom := hhorizontal a.im hai.ne _hs.1
  have htop := hhorizontal b.im hib.ne' _hs.2.1
  have hright : Complex.I *
      (∫ y : ℝ in a.im..b.im, 1 / (b.re + y * Complex.I - z)) =
      Complex.log (b.re + b.im * Complex.I - z) -
        Complex.log (b.re + a.im * Complex.I - z) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ ↦ Complex.log (b.re + y * Complex.I - z)) _
      (_hs.2.2.1.const_mul Complex.I)
    intro y hy
    have hslit : (b.re : ℂ) + y * Complex.I - z ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      left
      simpa using sub_pos.mpr hrb
    simpa only [one_mul, Pi.neg_apply, div_eq_mul_inv, inv_neg, neg_mul_neg] using!
      (((hcast y).mul_const Complex.I).const_add (b.re : ℂ) |>.sub_const z).clog_real hslit
  have hleft : Complex.I *
      (∫ y : ℝ in a.im..b.im, 1 / (a.re + y * Complex.I - z)) =
      Complex.log (-(a.re + b.im * Complex.I - z)) -
        Complex.log (-(a.re + a.im * Complex.I - z)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ ↦ Complex.log (-(a.re + y * Complex.I - z))) _
      (_hs.2.2.2.const_mul Complex.I)
    intro y hy
    have hslit : -((a.re : ℂ) + y * Complex.I - z) ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      left
      simpa using neg_pos.mpr (sub_neg.mpr har)
    simpa only [one_mul, Pi.neg_apply, div_eq_mul_inv, inv_neg, neg_mul_neg] using!
      ((((hcast y).mul_const Complex.I).const_add (a.re : ℂ) |>.sub_const z).neg).clog_real hslit
  have hupper : Complex.log (-(a.re + b.im * Complex.I - z)) =
      Complex.log (a.re + b.im * Complex.I - z) - Real.pi * Complex.I := by
    rw [Complex.log, Complex.log, norm_neg,
      Complex.arg_neg_eq_arg_sub_pi_of_im_pos (by simpa using sub_pos.mpr hib)]
    push_cast
    ring
  have hlower : Complex.log (-(a.re + a.im * Complex.I - z)) =
      Complex.log (a.re + a.im * Complex.I - z) + Real.pi * Complex.I := by
    rw [Complex.log, Complex.log, norm_neg,
      Complex.arg_neg_eq_arg_add_pi_of_im_neg (by simpa using sub_neg.mpr hai)]
    push_cast
    ring
  constructor
  rw [hbottom, htop, hright, hleft, hupper, hlower]
  ring

end HolomorphicAnosov.Analysis.Complex
