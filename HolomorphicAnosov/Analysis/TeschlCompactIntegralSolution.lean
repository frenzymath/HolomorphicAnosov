import Mathlib.Analysis.ODE.ExistUnique
import HolomorphicAnosov.Analysis.TeschlWholeIntegralSolution

/-! Auxiliary result for Teschl, Ordinary Differential Equations and Dynamical Systems,
Corollary 2.6 and estimate (2.29), pp. 40–41; Theorem 3.9, p. 81. -/

open Set Function MeasureTheory Metric intervalIntegral
open scoped Interval ContDiff NNReal Nat Topology _root_.Topology

namespace HolomorphicAnosov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a b t0 : ℝ}

lemma compact_integral_solution (hab : a ≤ b) (ht0 : t0 ∈ Icc a b)
    (A : ℝ → E →L[ℝ] E) (hA : ContinuousOn A (Icc a b)) (x0 : E) :
    ∃ x : ℝ → E, Continuous x ∧
      (∀ t ∈ Icc a b, x t = x0 + ∫ s in t0..t, A s (x s)) ∧
      (∀ t ∈ Icc a b, HasDerivAt x (A t (x t)) t) := by
  let B : ℝ → E →L[ℝ] E := IccExtend hab (fun t ↦ A t)
  have hB : Continuous B := Continuous.Icc_extend'
    (continuousOn_iff_continuous_domRestrict.mp hA)
  have hBA : EqOn B A (Icc a b) := fun t ht ↦ IccExtend_of_mem hab _ ht
  obtain ⟨x, hx, heq, hd⟩ := whole_integral_solution hab ht0 B hB x0
  refine ⟨x, hx, ?_, ?_⟩
  · intro t ht
    rw [heq t ht]
    congr 1
    exact integral_congr (fun s hs ↦ congrArg (fun L : E →L[ℝ] E ↦ L (x s))
      (hBA (uIcc_subset_Icc ht0 ht hs)))
  · intro t ht
    simpa only [hBA ht] using hd t ht

end HolomorphicAnosov
