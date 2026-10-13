import HolomorphicAnosov.Topology.CairnsGapNullFamily
import HolomorphicAnosov.Topology.CairnsResidualContactsDense
import HolomorphicAnosov.Topology.CairnsResidualSectorGeometry

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement
open scoped _root_.Topology

/-- The actual source residual sectors shrink uniformly for every recorded
Cairns recurrence. Source: Cairns §4(C), the corollary of Lemma 4.1, p.865.
Contact density makes all late angular gaps small. Uniform continuity puts
their image arcs in small disks; the sector convex-containment theorem puts
whole sector closures in the same disks, bounding their diameters. -/
theorem cairns_residual_source_sectors_shrink
    {σ : Circle → ℂ} {a : Set ℂ} {p q : Circle} {h : range σ ≃ₜ Circle}
    (hσ : Topology.IsEmbedding σ)
    (ha : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (haBounded : Bornology.IsBounded a) (d : Data σ a p q h) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      ∀ i : ResidualComponent ((d.stages n).contacts σ),
        Metric.diam (closure ((d.steps n).star i).sector) < ε := by
  intro ε hε
  obtain ⟨δ,hδ,hδspec⟩ := CairnsCircleGap.small_gap_image_subset_ball σ hσ.continuous
    (ε / 4) (by positivity)
  obtain ⟨N,hN⟩ := CairnsCircleGap.gap_length_eventually_lt_of_dense
    (fun n ↦ (d.stages n).contacts σ)
    (cairns_residual_star_recurrence_properties d).2.2.1
    (cairns_residual_stage_contacts_dense hσ d) δ hδ
  refine ⟨N,?_⟩
  intro n hn i
  let g := (d.steps n).gap i
  have harc : σ '' g.closedArc ⊆ Metric.closedBall (σ g.first) (ε / 4) :=
    (hδspec g (hN n hn g ((d.steps n).gap_isGap i))).trans Metric.ball_subset_closedBall
  have hsector := cairns_star_sector_closure_subset_closedBall hσ ha haBounded
    ((d.steps n).star i) (σ g.first) (ε / 4) harc
  have hdiam : Metric.diam (closure ((d.steps n).star i).sector) ≤ 2 * (ε / 4) := by
    apply Metric.diam_le_of_forall_dist_le (by positivity)
    intro x hx y hy
    have hx' := hsector hx
    have hy' := hsector hy
    change dist x (σ g.first) ≤ ε / 4 at hx'
    change dist y (σ g.first) ≤ ε / 4 at hy'
    have hh := dist_triangle x (σ g.first) y
    rw [dist_comm (σ g.first) y] at hh
    linarith
  linarith

/-- Any target sector family with the stated closed-disk confinement shrinks
uniformly along the same recurrence. Source: Cairns §4(C), p.865. Only the
continuous prescribed boundary parametrization is used in the target estimate. -/
theorem cairns_residual_target_sectors_shrink
    {σ : Circle → ℂ} {a : Set ℂ} {p q : Circle} {h : range σ ≃ₜ Circle}
    (hσ : Topology.IsEmbedding σ) (d : Data σ a p q h)
    (βt : ∀ n, ResidualComponent ((d.stages n).contacts σ) → Set ℂ)
    (hcontrol : ∀ n i z r,
      (fun t : Circle ↦ (h ⟨σ t,⟨t,rfl⟩⟩ : ℂ)) '' ((d.steps n).gap i).closedArc ⊆
        Metric.closedBall z r → closure (βt n i) ⊆ Metric.closedBall z r) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      ∀ i : ResidualComponent ((d.stages n).contacts σ), Metric.diam (closure (βt n i)) < ε := by
  let τ := fun t : Circle ↦ (h ⟨σ t,⟨t,rfl⟩⟩ : ℂ)
  have hτ : Continuous τ := continuous_subtype_val.comp
    (h.continuous.comp (hσ.continuous.subtype_mk (fun t ↦ ⟨t,rfl⟩)))
  intro ε hε
  obtain ⟨δ,hδ,hδspec⟩ := CairnsCircleGap.small_gap_image_subset_ball τ hτ
    (ε / 4) (by positivity)
  obtain ⟨N,hN⟩ := CairnsCircleGap.gap_length_eventually_lt_of_dense
    (fun n ↦ (d.stages n).contacts σ)
    (cairns_residual_star_recurrence_properties d).2.2.1
    (cairns_residual_stage_contacts_dense hσ d) δ hδ
  refine ⟨N,?_⟩
  intro n hn i
  let g := (d.steps n).gap i
  have harc : τ '' g.closedArc ⊆ Metric.closedBall (τ g.first) (ε / 4) :=
    (hδspec g (hN n hn g ((d.steps n).gap_isGap i))).trans Metric.ball_subset_closedBall
  have hsector := hcontrol n i (τ g.first) (ε / 4) harc
  have hdiam : Metric.diam (closure (βt n i)) ≤ 2 * (ε / 4) := by
    apply Metric.diam_le_of_forall_dist_le (by positivity)
    intro x hx y hy
    have hx' := hsector hx
    have hy' := hsector hy
    change dist x (τ g.first) ≤ ε / 4 at hx'
    change dist y (τ g.first) ≤ ε / 4 at hy'
    have hh := dist_triangle x (τ g.first) y
    rw [dist_comm (τ g.first) y] at hh
    linarith
  linarith

end HolomorphicAnosov.Topology.Plane
