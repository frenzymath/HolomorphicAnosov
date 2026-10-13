import Mathlib.Analysis.ODE.ExistUnique
import HolomorphicAnosov.Analysis.TeschlPicardIterateBound

/-! Auxiliary result for Teschl, Ordinary Differential Equations and Dynamical Systems,
Corollary 2.6 and estimate (2.29), pp. 40–41; Theorem 3.9, p. 81. -/

open Set Function MeasureTheory Metric intervalIntegral
open scoped Interval ContDiff NNReal Nat Topology _root_.Topology

namespace HolomorphicAnosov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a b t0 : ℝ}

lemma wholeNext_exists_fixed (hab : a ≤ b) (ht0 : t0 ∈ Icc a b)
    (A : ℝ → E →L[ℝ] E) (hA : Continuous A) (x0 : E) (K : ℝ≥0)
    (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K) :
    ∃ α : C(Icc a b, E), IsFixedPt (wholeNext (t0 := t0) hab A hA x0) α := by
  obtain ⟨m, hm⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop
    (K * max (b - t0) (t0 - a)) |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have hnonneg : (0 : ℝ) ≤ (K * max (b - t0) (t0 - a)) ^ m / m.factorial := by
    have : 0 ≤ max (b - t0) (t0 - a) := le_max_of_le_left (sub_nonneg.mpr ht0.2)
    positivity
  -- The factorial decay supplies a contracting iterate on the WHOLE curve space.
  have hcontract : ContractingWith ⟨_, hnonneg⟩
      (wholeNext (t0 := t0) hab A hA x0)^[m] := by
    refine ⟨hm, LipschitzWith.of_dist_le_mul fun α β ↦ ?_⟩
    rw [ContinuousMap.dist_le]
    · intro t
      apply (wholeNext_iterate_bound hab ht0 A hA x0 K hK α β m t).trans
      change _ ≤ ((K * max (b - t0) (t0 - a)) ^ m / m.factorial) * dist α β
      gcongr
      exact abs_sub_le_max_sub t.2.1 t.2.2 _
    · positivity
  exact ⟨_, hcontract.isFixedPt_fixedPoint_iterate⟩

end HolomorphicAnosov
