import Mathlib.Analysis.ODE.ExistUnique

/-! Auxiliary result for Teschl, Ordinary Differential Equations and Dynamical Systems,
Corollary 2.6 and estimate (2.29), pp. 40–41; Theorem 3.9, p. 81. -/

open Set Function MeasureTheory Metric intervalIntegral
open scoped Interval ContDiff NNReal Nat Topology _root_.Topology

namespace HolomorphicAnosov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a b t0 : ℝ}

omit [CompleteSpace E] in
lemma solution_contDiff_one {x : ℝ → E}
    (A : ℝ → E →L[ℝ] E) (hA : ContinuousOn A (Ioo a b))
    (hx : ContinuousOn x (Ioo a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt x (A t (x t)) t) :
    ContDiffOn ℝ 1 x (Ioo a b) := by
  rw [contDiffOn_one_iff_derivWithin isOpen_Ioo.uniqueDiffOn]
  refine ⟨fun t ht ↦ (hd t ht).differentiableAt.differentiableWithinAt, ?_⟩
  exact (hA.clm_apply hx).congr (fun t ht ↦
    ((hd t ht).hasDerivWithinAt.derivWithin (isOpen_Ioo.uniqueDiffWithinAt ht)))

end HolomorphicAnosov
