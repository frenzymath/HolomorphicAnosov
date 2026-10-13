import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter

open Set Filter _root_.Topology
open scoped BigOperators ENNReal Classical
noncomputable section

/-- Cap the original extended distance by a positive finite constant. Minimum preserves the triangle inequality; balls at radii smaller than the cap are unchanged, so the topology is unchanged. Mathlib converts the resulting finite extended metric to a metric. No data is admitted. -/
@[instance_reducible]
noncomputable def cappedMetric {X : Type*} [EMetricSpace X]
    (c : ℝ≥0∞) (hc : 0 < c) (hct : c ≠ ⊤) : MetricSpace X := by
  let p : PseudoEMetricSpace X := PseudoEMetricSpace.ofEDistOfTopology
    (fun x y ↦ min c (edist x y)) (by simp)
    (by intro x y; simp only [edist_comm])
    (by intro x y z; grw [edist_triangle x y z, min_add_distrib, min_le_right])
    (fun x ↦ Metric.nhds_basis_eball.to_hasBasis
      (by
        intro r hr
        refine ⟨min r c, lt_min hr hc, ?_⟩
        intro y hy
        have hd : edist x y < min r c := by
          change min c (edist x y) < min r c at hy
          rcases min_lt_iff.mp hy with h | h
          · exact False.elim ((not_lt_of_ge (min_le_right r c)) h)
          · exact h
        exact (by simpa only [Metric.mem_eball, edist_comm] using hd.trans_le (min_le_left r c)))
      (by
        intro r hr
        refine ⟨r, hr, ?_⟩
        intro y hy
        have hd : edist x y < r := by simpa only [Metric.mem_eball, edist_comm] using hy
        exact (min_le_right c (edist x y)).trans_lt hd))
  letI : PseudoEMetricSpace X := p
  letI : EMetricSpace X := EMetricSpace.ofT0PseudoEMetricSpace X
  exact EMetricSpace.toMetricSpace fun x y ↦
    ne_top_of_le_ne_top hct (min_le_left c _)


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter
