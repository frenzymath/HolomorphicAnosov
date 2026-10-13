import Mathlib.Analysis.ODE.ExistUnique
import HolomorphicAnosov.Analysis.TeschlPicardOperator

/-! Auxiliary result for Teschl, Ordinary Differential Equations and Dynamical Systems,
Corollary 2.6 and estimate (2.29), pp. 40–41; Theorem 3.9, p. 81. -/

open Set Function MeasureTheory Metric intervalIntegral
open scoped Interval ContDiff NNReal Nat Topology _root_.Topology

namespace HolomorphicAnosov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a b t0 : ℝ}

lemma wholeNext_apply (hab : a ≤ b)
    (A : ℝ → E →L[ℝ] E) (hA : Continuous A) (x0 : E)
    (α : C(Icc a b, E)) (t : Icc a b) :
    wholeNext (t0 := t0) hab A hA x0 α t = x0 + ∫ s in t0..t, A s (IccExtend hab α s) := rfl

end HolomorphicAnosov
