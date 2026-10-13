import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Group.Constructions

open Filter
open scoped Topology _root_.Topology

namespace HolomorphicAnosov





theorem hps_normalized_zero_bounded
    {E : Type*} [NormedAddCommGroup E] (w : ℕ → E) (ρ : ℝ)
    (h : Tendsto (fun n ↦ ‖w n‖ / ρ ^ n) atTop (𝓝 0)) :
    ∃ M : ℝ, ∀ n, ‖w n‖ / ρ ^ n ≤ M := by
  obtain ⟨M, hM⟩ := (Metric.isBounded_range_of_tendsto _ h).bddAbove
  exact ⟨M, fun n ↦ hM (Set.mem_range_self n)⟩

end HolomorphicAnosov
