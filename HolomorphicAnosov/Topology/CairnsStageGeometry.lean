import HolomorphicAnosov.Topology.CairnsResidualStarRefinement

namespace HolomorphicAnosov.Topology.Plane.CairnsRefinement
open Set CairnsStar

/-- The geometric invariant proved for the literal initial stage and preserved
by the actual outside-star successor. This is a proof record, not data assumed
in the raw recurrence: its witnesses are produced by disk-cell gluing and
compact null-family pasting. Source: Cairns §4(B,C). -/
structure StageGeometry (σ : Circle → ℂ) (a : Set ℂ) (h : range σ ≃ₜ Circle)
    (s : Stage) : Prop where
  nonempty : s.region.Nonempty
  isOpen : IsOpen s.region
  subset : s.region ⊆ a
  connected : IsConnected s.region
  four : ∃ t₁ t₂ t₃ t₄ : Circle,
    t₁ ∈ s.contacts σ ∧ t₂ ∈ s.contacts σ ∧ t₃ ∈ s.contacts σ ∧ t₄ ∈ s.contacts σ ∧
    t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₁ ≠ t₄ ∧ t₂ ≠ t₃ ∧ t₂ ≠ t₄ ∧ t₃ ≠ t₄
  curve : ∀ (z : ℂ) (hz : z ∈ range σ), s.map z = (h ⟨z,hz⟩ : ℂ)
  chord : ∀ g : CairnsCircleGap, g.IsGapOf (s.contacts σ) →
    openSegment ℝ (σ g.first) (σ g.last) ⊆ a ∩ frontier s.region
  affine : ∀ g : CairnsCircleGap, g.IsGapOf (s.contacts σ) → ∀ t : I,
    s.map ((1-(t : ℝ)) • σ g.first + (t : ℝ) • σ g.last) =
      (1-(t : ℝ)) • (h ⟨σ g.first,⟨g.first,rfl⟩⟩ : ℂ) +
        (t : ℝ) • (h ⟨σ g.last,⟨g.last,rfl⟩⟩ : ℂ)
  source_frontier : ∀ gap : ResidualComponent (s.contacts σ) → CairnsCircleGap,
    (∀ i, (gap i).IsGapOf (s.contacts σ)) → (∀ i, (gap i).openArc = i.val) →
    frontier s.region = σ '' s.contacts σ ∪
      ⋃ i, openSegment ℝ (σ (gap i).first) (σ (gap i).last)
  target_nonempty : s.target.Nonempty
  target_open : IsOpen s.target
  target_ball : s.target ⊆ Metric.ball (0 : ℂ) 1
  target_convex : Convex ℝ s.target
  target_closure : closure s.target = convexHull ℝ
    ((fun t : Circle ↦ (h ⟨σ t,⟨t,rfl⟩⟩ : ℂ)) '' s.contacts σ)
  carrier : ∃ H : ↥(closure s.region ∪ range σ) ≃ₜ
    ↥(closure s.target ∪ range (fun z : Circle ↦ (z : ℂ))),
    ∀ x, (H x : ℂ) = s.map x
  cell : ∃ G : closure s.region ≃ₜ Metric.closedBall (0 : ℂ) 1,
    G '' {z : closure s.region | (z : ℂ) ∈ s.region} =
      {w : Metric.closedBall (0 : ℂ) 1 | (w : ℂ) ∈ Metric.ball (0 : ℂ) 1} ∧
    G '' {z : closure s.region | (z : ℂ) ∈ frontier s.region} =
      {w : Metric.closedBall (0 : ℂ) 1 | (w : ℂ) ∈ Metric.sphere (0 : ℂ) 1}

end HolomorphicAnosov.Topology.Plane.CairnsRefinement
