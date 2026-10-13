import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Homotopy.Contractible

namespace HolomorphicAnosov

/-- A weakly locally contractible compact metric subspace has arbitrarily small
centered relative balls whose inclusion into a prescribed centered relative ball
is nullhomotopic.

Source: Hatcher, *Algebraic Topology*, Theorem A.7, pp.525–526. This is the
local ball selection used before the cell-by-cell controlled extension. Restrict
the given nullhomotopy to a smaller centered ball and compose inclusions. -/
theorem hatcher_centered_nullhomotopic_ball
    {X : Type*} [PseudoMetricSpace X]
    (C : Set X)
    (hlocal : ∀ (c : C) (O : Set C), IsOpen O → c ∈ O →
      ∃ V : Set C, IsOpen V ∧ c ∈ V ∧
        ∃ hVO : V ⊆ O, (ContinuousMap.inclusion hVO).Nullhomotopic)
    (c : C) (R : ℝ) (hR : 0 < R) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧
      ∃ hsub : Metric.ball c r ⊆ Metric.ball c R,
        (ContinuousMap.inclusion hsub).Nullhomotopic := by
  obtain ⟨V, hVo, hcV, hVO, hnull⟩ :=
    hlocal c (Metric.ball c R) Metric.isOpen_ball (Metric.mem_ball_self hR)
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hVo c hcV
  let t := min r (R / 2)
  have ht : 0 < t := lt_min hr (half_pos hR)
  have htR : t < R := (min_le_right _ _).trans_lt (half_lt_self hR)
  have htV : Metric.ball c t ⊆ V :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hrV
  refine ⟨t, ht, htR, htV.trans hVO, ?_⟩
  simpa only [ContinuousMap.inclusion_comp_inclusion] using
    hnull.comp_left (ContinuousMap.inclusion htV)

end HolomorphicAnosov
