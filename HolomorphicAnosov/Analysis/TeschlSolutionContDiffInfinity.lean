import Mathlib.Analysis.ODE.ExistUnique

/-! Auxiliary result for Teschl, Ordinary Differential Equations and Dynamical Systems,
Corollary 2.6 and estimate (2.29), pp. 40–41; Theorem 3.9, p. 81. -/

open Set Function MeasureTheory Metric intervalIntegral
open scoped Interval ContDiff NNReal Nat Topology _root_.Topology

namespace HolomorphicAnosov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a b t0 : ℝ}

omit [CompleteSpace E] in
lemma solution_contDiff_infty {x : ℝ → E}
    (A : ℝ → E →L[ℝ] E) (hA : ContDiffOn ℝ ∞ A (Ioo a b))
    (hx : ContinuousOn x (Ioo a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt x (A t (x t)) t) :
    ContDiffOn ℝ ∞ x (Ioo a b) := by
  have hn (k : ℕ) : ContDiffOn ℝ k x (Ioo a b) := by
    induction k with
    | zero => simpa only [Nat.cast_zero, contDiffOn_zero] using hx
    | succ k ih =>
      rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
      refine ⟨fun t ht ↦ (hd t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      exact ((hA.of_le (by simp)).clm_apply ih).congr (fun t ht ↦ (hd t ht).deriv)
  rw [contDiffOn_infty]
  exact hn

end HolomorphicAnosov
