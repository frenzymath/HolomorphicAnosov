import HolomorphicAnosov.Topology.CairnsTargetBoundaryContacts
import HolomorphicAnosov.Topology.CairnsStageTargetChords
import HolomorphicAnosov.Topology.CairnsOutsideSectorSelection

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- Each target gap has an outside chord sector with the required component,
frontier and convex disk confinement properties. The target circle embedding
has the disk as its bounded component. Its old contact set equals the source
contact set, and affine carrier transport identifies the gap's frontier chord.
Three retained contacts select the outside side of that chord. Source: Cairns
§4(C), paired source and target residual sectors. -/
theorem cairns_target_sector_selection
    {σ : Circle → ℂ} {a : Set ℂ} {s : Stage}
    (hσ : Topology.IsEmbedding σ) (hab : Bornology.IsBounded a)
    (h : range σ ≃ₜ Circle) (hs : StageGeometry σ a h s)
    (g : CairnsCircleGap) (hg : g.IsGapOf (s.contacts σ)) :
    let τ := fun t : Circle ↦ (h ⟨σ t,⟨t,rfl⟩⟩ : ℂ)
    ∃ b : StarChoice τ (Metric.ball (0 : ℂ) 1) g,
      Disjoint b.sector s.target ∧
      b.sector.Nonempty ∧ IsOpen b.sector ∧ IsConnected b.sector ∧
      (∃ x ∈ Metric.ball (0 : ℂ) 1 \ closure s.target,
        connectedComponentIn (Metric.ball (0 : ℂ) 1 \ closure s.target) x = b.sector) ∧
      (∀ z r, τ '' g.closedArc ⊆ Metric.closedBall z r →
        closure b.sector ⊆ Metric.closedBall z r) := by
  intro τ
  obtain ⟨hτ,hτrange,hcomponent⟩ := cairns_target_boundary_geometry hσ h
  have hτcontacts : τ ⁻¹' closure s.target = s.contacts σ :=
    cairns_target_stage_contacts h hs
  let ht : range τ ≃ₜ Circle := Homeomorph.setCongr
    (hτrange.trans (show range (fun z : Circle ↦ (z : ℂ)) = Metric.sphere (0 : ℂ) 1
      from Subtype.range_coe))
  have hthree : ∃ p q r : Circle,
      τ p ∈ closure s.target ∧ τ q ∈ closure s.target ∧ τ r ∈ closure s.target ∧
      p ≠ q ∧ p ≠ r ∧ q ≠ r := by
    obtain ⟨p,q,r,t,hp,hq,hr,_,hpq,hpr,_,hqr,_,_⟩ := hs.four
    rw [← hτcontacts] at hp hq hr
    exact ⟨p,q,r,hp,hq,hr,hpq,hpr,hqr⟩
  have hne : g.first ≠ g.last := by
    intro he
    exact g.start_lt_stop.ne (Circle.exp_injOn_Icc g.shorter_than_turn
      ⟨le_rfl,g.start_lt_stop.le⟩ ⟨g.start_lt_stop.le,le_rfl⟩ he)
  have hchord : openSegment ℝ (τ g.first) (τ g.last) ⊆ Metric.ball (0 : ℂ) 1 :=
    openSegment_subset_ball_of_ne
      (Metric.sphere_subset_closedBall (h ⟨σ g.first,⟨g.first,rfl⟩⟩).property)
      (Metric.sphere_subset_closedBall (h ⟨σ g.last,⟨g.last,rfl⟩⟩).property)
      (hτ.injective.ne hne)
  have hfront : openSegment ℝ (τ g.first) (τ g.last) ⊆ frontier s.target :=
    cairns_stage_target_gap_chord hab h hs g hg
  obtain ⟨b,hgeo,hout⟩ := cairns_choose_outside_geometric_star τ hτ
    (Metric.ball (0 : ℂ) 1) ⟨0,by simp⟩ Metric.isBounded_ball hcomponent ht s.target
    hs.target_open hs.target_convex.isPreconnected hs.target_ball hthree g
    (hτcontacts ▸ hg) hchord hfront
  obtain ⟨hne,ho,hc,_⟩ := cairns_star_sector_geometry hτ hcomponent b
  exact ⟨b,hout,hne,ho,hc,
    cairns_star_sector_component_outside_closure hτ hcomponent b s.target hout
      (hfront.trans frontier_subset_closure),
    fun z r harc ↦ cairns_star_sector_closure_subset_closedBall hτ hcomponent
      Metric.isBounded_ball b z r harc⟩

end HolomorphicAnosov.Topology.Plane

