import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open Set
namespace HolomorphicAnosov.Analysis.MarkedRectangle

/-!
# The downward logarithm branch on the closed upper half-plane

DAG: `analysis.complex_downward_log_g5`.
Source: Bak–Newman, *Complex Analysis*, third edition (2010), pp.188–190,
positive-to-the-right branch with downward cuts. The explicit logarithm identity
is the guarded multiplication law in pinned Mathlib `Complex.log_mul`; the
argument interval below verifies its hypotheses, including both real half-axes.
-/

/-- Rotating a nonzero closed-upper-half-plane argument by -i puts it in the
principal slit plane, and subtracting log(-i) recovers its principal logarithm.
Source: Bak–Newman pp.188–190 and Mathlib's guarded logarithm multiplication law.
Proof: arg(v) lies in [0,pi], so arg(-i)+arg(v) lies in [-pi/2,pi/2], inside
(-pi,pi]. Apply log_mul and cancel log(-i). The rotated real part is Im(v):
if positive it avoids the cut, and if zero its imaginary part -Re(v) is nonzero. -/
theorem downwardLog_upperHalfPlane {v : ℂ} (hv : v ≠ 0) (him : 0 ≤ v.im) :
    Complex.log (-Complex.I * v) - Complex.log (-Complex.I) = Complex.log v ∧
      -Complex.I * v ∈ Complex.slitPlane := by
  constructor
  · have harg : (-Complex.I).arg + v.arg ∈ Ioc (-Real.pi) Real.pi := by
      rw [Complex.arg_neg_I]
      have ha := Complex.arg_nonneg_iff.mpr him
      have hb := Complex.arg_le_pi v
      constructor <;> linarith [Real.pi_pos]
    rw [Complex.log_mul (neg_ne_zero.mpr Complex.I_ne_zero) hv harg]
    ring
  · apply Complex.mem_slitPlane_iff.mpr
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, zero_mul, zero_sub, neg_mul, one_mul,
      neg_neg, zero_add]
    by_cases h : v.im = 0
    · right
      have hreal : v.re ≠ 0 := by
        intro hr
        exact hv (Complex.ext hr h)
      exact neg_ne_zero.mpr hreal
    · left
      exact lt_of_le_of_ne him (Ne.symm h)

end HolomorphicAnosov.Analysis.MarkedRectangle
