import HolomorphicAnosov.Topology.CairnsStageGeometry
import HolomorphicAnosov.Topology.CairnsClosedCellRestriction

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- Restrict the stage's closed-disk cell chart to its interior and frontier.
The recorded image equalities identify these restrictions with the unit open
disk and unit circle. Source: Cairns §4(B,C), stage disk invariant. -/
theorem cairns_stage_disk_charts
    {σ : Circle → ℂ} {a : Set ℂ} {h : range σ ≃ₜ Circle} {s : Stage}
    (hs : StageGeometry σ a h s) :
    Nonempty (s.region ≃ₜ Metric.ball (0 : ℂ) 1) ∧
      Nonempty (Circle ≃ₜ frontier s.region) := by
  obtain ⟨G,hi,hf⟩ := hs.cell
  have hmem (P Q : Set ℂ)
      (hPQ : G '' {x : closure s.region | (x : ℂ) ∈ P} =
        {y : Metric.closedBall (0 : ℂ) 1 | (y : ℂ) ∈ Q})
      (x : closure s.region) : (x : ℂ) ∈ P ↔ (G x : ℂ) ∈ Q := by
    change x ∈ {x : closure s.region | (x : ℂ) ∈ P} ↔ _
    rw [← G.injective.mem_set_image]
    rw [hPQ]
    rfl
  exact ⟨⟨homeomorphRestrictSubsets _ _ s.region (Metric.ball (0 : ℂ) 1)
    subset_closure Metric.ball_subset_closedBall G (hmem _ _ hi)⟩,
    ⟨(homeomorphRestrictSubsets _ _ (frontier s.region) (Metric.sphere (0 : ℂ) 1)
      frontier_subset_closure Metric.sphere_subset_closedBall G (hmem _ _ hf)).symm⟩⟩

end HolomorphicAnosov.Topology.Plane
