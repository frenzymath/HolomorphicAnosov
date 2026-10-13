import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open Set
namespace HolomorphicAnosov.Analysis.MarkedRectangle

/-!
# Real boundary values of the positive inverse-square-root branch

DAG: `analysis.complex_inverse_sqrt_real_boundary_g5`.
Source: Bak–Newman, *Complex Analysis*, third edition (2010), pp.188–189,
semicircular branch calculation and the branch positive to the right of a real vertex.
-/

/-- The positive-to-the-right inverse-square-root branch has phase -i on the
negative real axis and phase one on the positive real axis.
Source: Bak–Newman pp.188–189. For r>0 use the real logarithm and exponential.
For r<0, write log(r)=log(-r)+pi*i; exponential addition and exp(-pi*i/2)=-i
supply the phase. Absolute value gives the displayed positive amplitude in both cases.
Zero is excluded because it is the branch point. -/
theorem inverseSqrt_real_boundary {r : ℝ} (hr : r ≠ 0) :
    Complex.exp (-Complex.log (r : ℂ) / 2) =
      (if r < 0 then -Complex.I else 1) *
        (Real.exp (-Real.log |r| / 2) : ℂ) := by
  by_cases h : r < 0
  · rw [ite_eq_left h, abs_of_neg h]
    have hlog : Complex.log (r : ℂ) = (Real.log (-r) : ℂ) + Real.pi * Complex.I := by
      have hmul := Complex.log_ofReal_mul (neg_pos.mpr h) (show (-1 : ℂ) ≠ 0 by norm_num)
      simpa [Complex.log_neg_one] using hmul
    rw [hlog]
    have he : -((Real.log (-r) : ℂ) + Real.pi * Complex.I) / 2 =
        ((-Real.log (-r) / 2 : ℝ) : ℂ) + (-(Real.pi : ℂ) / 2) * Complex.I := by
      push_cast
      ring
    rw [he, Complex.exp_add, Complex.exp_neg_pi_div_two_mul_I]
    rw [← Complex.ofReal_exp]
    ring
  · have hp : 0 < r := lt_of_le_of_ne (le_of_not_gt h) hr.symm
    rw [ite_eq_right h, abs_of_pos hp, one_mul, ← Complex.ofReal_log hp.le]
    norm_cast

end HolomorphicAnosov.Analysis.MarkedRectangle
