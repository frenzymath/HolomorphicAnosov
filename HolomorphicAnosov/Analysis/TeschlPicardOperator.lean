import Mathlib.Analysis.ODE.ExistUnique

/-! Auxiliary result for Teschl, Ordinary Differential Equations and Dynamical Systems,
Corollary 2.6 and estimate (2.29), pp. 40–41; Theorem 3.9, p. 81. -/

open Set Function MeasureTheory Metric intervalIntegral
open scoped Interval ContDiff NNReal Nat Topology _root_.Topology

namespace HolomorphicAnosov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a b t0 : ℝ}

noncomputable def wholeNext (hab : a ≤ b)
    (A : ℝ → E →L[ℝ] E) (hA : Continuous A) (x0 : E)
    (α : C(Icc a b, E)) : C(Icc a b, E) where
  toFun t := x0 + ∫ s in t0..t, A s (IccExtend hab α s)
  continuous_toFun := by
    have hc : Continuous (fun s ↦ A s (IccExtend hab α s)) :=
      hA.clm_apply (α.continuous.Icc_extend')
    exact (continuous_const.add
      (differentiable_integral_of_continuous hc).continuous).comp continuous_subtype_val

end HolomorphicAnosov
