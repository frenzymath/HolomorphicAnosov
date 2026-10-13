import HolomorphicAnosov.Analysis.Regularity.PolynomialBallDerivativeEstimate
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace HolomorphicAnosov

open Filter
open scoped Topology _root_.Topology

lemma approximation_remainder_hasFDerivAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (a : E)
    (C r s : ℝ) (_hC : 0 ≤ C) (hr : 0 < r) (hs : 1 < s)
    (hf : ∀ y ∈ Metric.ball a r, |f y| ≤ C * ‖y - a‖ ^ s) :
    HasFDerivAt f (0 : E →L[ℝ] ℝ) a := by
  have hfa : f a = 0 := by
    have he := hf a (Metric.mem_ball_self hr)
    simp only [sub_self, norm_zero, Real.zero_rpow (by linarith : s ≠ 0),
      mul_zero] at he
    exact abs_nonpos_iff.mp he
  apply hasFDerivAt_iff_isLittleO.mpr
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have ht : Tendsto (fun y : E ↦ C * ‖y - a‖ ^ (s - 1)) (𝓝 a) (𝓝 0) := by
    have hpow := (Real.continuousAt_rpow_const 0 (s - 1) (Or.inr (by linarith))).tendsto.comp
      (tendsto_norm_sub_self a)
    simpa only [Function.comp_def, Real.zero_rpow (by linarith : s - 1 ≠ 0), mul_zero] using
      hpow.const_mul C
  filter_upwards [Metric.ball_mem_nhds a hr, ht.eventually (gt_mem_nhds hε)] with y hy hsmall
  change ‖f y - f a - (0 : E →L[ℝ] ℝ) (y - a)‖ ≤ ε * ‖y - a‖
  simp only [hfa, sub_zero, zero_apply]
  rw [Real.norm_eq_abs]
  have he := hf y hy
  have hid : ‖y - a‖ ^ s = ‖y - a‖ ^ (s - 1) * ‖y - a‖ := by
    have he := Real.rpow_add_of_nonneg (norm_nonneg (y - a))
      (by linarith : 0 ≤ s - 1) zero_le_one
    simpa only [sub_add_cancel, Real.rpow_one] using he
  rw [hid, ← mul_assoc] at he
  exact he.trans (mul_le_mul_of_nonneg_right hsmall.le (norm_nonneg _))

-- The constant translated coefficient evaluates the same original polynomial.


end HolomorphicAnosov
