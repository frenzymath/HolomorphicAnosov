import Mathlib.Analysis.ODE.ExistUnique
import HolomorphicAnosov.Analysis.TeschlPicardFixedPoint

/-! Auxiliary result for Teschl, Ordinary Differential Equations and Dynamical Systems,
Corollary 2.6 and estimate (2.29), pp. 40–41; Theorem 3.9, p. 81. -/

open Set Function MeasureTheory Metric intervalIntegral
open scoped Interval ContDiff NNReal Nat Topology _root_.Topology

namespace HolomorphicAnosov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a b t0 : ℝ}

lemma whole_integral_solution (hab : a ≤ b) (ht0 : t0 ∈ Icc a b)
    (A : ℝ → E →L[ℝ] E) (hA : Continuous A) (x0 : E) :
    ∃ x : ℝ → E, Continuous x ∧
      (∀ t ∈ Icc a b, x t = x0 + ∫ s in t0..t, A s (x s)) ∧
      (∀ t ∈ Icc a b, HasDerivAt x (A t (x t)) t) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hA.continuousOn
  let K : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K :=
    fun t ht ↦ (hC t ht).trans (le_max_left _ _)
  obtain ⟨α, hα⟩ := wholeNext_exists_fixed hab ht0 A hA x0 K hK
  -- The primitive of the continuously extended integrand has full endpoint derivatives.
  let x : ℝ → E := fun t ↦ x0 + ∫ s in t0..t, A s (IccExtend hab α s)
  have hc : Continuous (fun s ↦ A s (IccExtend hab α s)) :=
    hA.clm_apply (α.continuous.Icc_extend')
  have heq : ∀ t ∈ Icc a b, x t = IccExtend hab α t := by
    intro t ht
    simpa only [wholeNext_apply, IccExtend_of_mem hab _ ht] using
      congrArg (fun u : C(Icc a b, E) ↦ u ⟨t, ht⟩) hα
  refine ⟨x, (continuous_const.add
    (differentiable_integral_of_continuous hc).continuous), ?_, ?_⟩
  · intro t ht
    change x0 + (∫ s in t0..t, A s (IccExtend hab α s)) = x0 + _
    congr 1
    apply integral_congr
    intro s hs
    dsimp only
    rw [heq s (uIcc_subset_Icc ht0 ht hs)]
  · intro t ht
    have hd := (integral_hasDerivAt_right (hc.intervalIntegrable t0 t)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add x0
    simpa only [← heq t ht] using hd

end HolomorphicAnosov
