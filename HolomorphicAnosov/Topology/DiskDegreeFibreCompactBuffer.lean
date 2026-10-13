import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace HolomorphicAnosov.Topology

open Metric

variable {X Y : Type*} [MetricSpace X] [ProperSpace X]
  [TopologicalSpace Y] [T2Space Y]

/--
 The fibre of a continuous map from a proper metric space to a Hausdorff space
 is compact in a closed ball,
 avoids the boundary when the boundary avoids the target, and is contained in
 a strictly smaller closed ball.  This is the compact boundary-buffer operand
 in the local degree argument.
 Source: Hatcher, Algebraic Topology, Proposition 2.30, p.136. The fibre is a closed
 subset of the compact ball. Boundary avoidance makes each distance strictly less than r.
 On a nonempty fibre maximize distance; on the empty fibre use r - 1.
-/
theorem disk_degree_fibre_compact_buffer
    (c : X) (r : ℝ)
    (g : X → Y)
    (hg : ContinuousOn g (Metric.closedBall c r))
    (w : Y)
    (hboundary : ∀ z ∈ Metric.sphere c r, g z ≠ w) :
    IsCompact {z : X | z ∈ Metric.closedBall c r ∧ g z = w} ∧
      {z : X | z ∈ Metric.closedBall c r ∧ g z = w} ⊆ Metric.ball c r ∧
      ∃ ρ < r,
        {z : X | z ∈ Metric.closedBall c r ∧ g z = w} ⊆
          Metric.closedBall c ρ := by
  let K := {z : X | z ∈ Metric.closedBall c r ∧ g z = w}
  have hclosed : IsClosed K :=
    hg.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton
  have hK : IsCompact K := (isCompact_closedBall c r).of_isClosed_subset hclosed
    (fun _ hz ↦ hz.1)
  have hinside : K ⊆ Metric.ball c r := by
    intro z hz
    exact lt_of_le_of_ne (mem_closedBall.mp hz.1) (fun he ↦ hboundary z he hz.2)
  refine ⟨hK, hinside, ?_⟩
  by_cases hne : K.Nonempty
  · obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hne
      (continuous_id.dist continuous_const).continuousOn
    exact ⟨dist z c, hinside hz, fun y hy ↦ hmax hy⟩
  · exact ⟨r - 1, by linarith, fun z hz ↦ False.elim (hne ⟨z, hz⟩)⟩

end HolomorphicAnosov.Topology
