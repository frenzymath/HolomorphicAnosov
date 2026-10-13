import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact

/-! DAG node: `topo.positive_coordinate_frontier_point_g10`. -/

open Set Metric
namespace HolomorphicAnosov

/-- A bounded open region meeting the positive side of an open real coordinate
has a frontier point on that side. Agent expansion of the frontier step in Cairns
(1951), Lemma 3.1(C). Maximize the coordinate on the compact closure. The maximum
is positive because of the given interior point. An interior maximum is impossible:
the open image of the region contains coordinate values larger than that maximum. -/
theorem positive_coordinate_frontier_point
    {X : Type*} [MetricSpace X] [ProperSpace X] {B : Set X}
    (hB : IsOpen B) (hb : Bornology.IsBounded B)
    (F : X → ℝ) (hc : Continuous F) (ho : IsOpenMap F)
    {x : X} (hx : x ∈ B) (hFx : 0 < F x) :
    ∃ y ∈ frontier B, 0 < F y := by
  obtain ⟨y, hy, hmax⟩ := hb.isCompact_closure.exists_isMaxOn
    ⟨x, subset_closure hx⟩ hc.continuousOn
  have hFy : 0 < F y := hFx.trans_le (hmax (subset_closure hx))
  refine ⟨y, ?_, hFy⟩
  rw [hB.frontier_eq]
  refine ⟨hy, ?_⟩
  intro hyB
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp (ho B hB) (F y) ⟨y, hyB, rfl⟩
  have hhalf : F y + δ/2 ∈ ball (F y) δ := by
    rw [mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hδ)]
    exact half_lt_self hδ
  obtain ⟨z, hz, hzF⟩ := hδsub hhalf
  have hle : F z ≤ F y := hmax (subset_closure hz)
  rw [hzF] at hle
  linarith

end HolomorphicAnosov

