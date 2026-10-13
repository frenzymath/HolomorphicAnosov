import HolomorphicAnosov.Topology.CairnsInitialStageGeometry
import HolomorphicAnosov.Topology.CairnsSuccessorStageGeometry
import HolomorphicAnosov.Topology.CairnsGeometricInitialChoice

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- Construct Cairns's actual infinite recurrence by induction on the proved
stage invariant. The initial two-star theorem supplies the initial invariant.
At each stage the actual contact gaps and old frontier select outside stars;
the successor theorem proves that their literal union and literal patch map
retain the invariant. Primitive recursion stores these stages, so both raw
recurrence equations hold by construction. Source: Cairns §4(B,C). -/
theorem cairns_geometric_recurrence
    (σ : Circle → ℂ) (hσ : Topology.IsEmbedding σ)
    (a : Set ℂ) (ha : a.Nonempty) (hab : Bornology.IsBounded a)
    (hacomp : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (h : range σ ≃ₜ Circle) (p q : Circle) (hpq : p ≠ q)
    (hchord : openSegment ℝ (σ p) (σ q) ⊆ a) :
    ∃ d : Data σ a p q h,
      (∀ j, StageGeometry σ a h (d.stages j)) ∧
      (∀ j i, StarGeometry ((d.steps j).star i) h) := by
  classical
  obtain ⟨initial,h₁,h₂,ho₁,ho₂,hdis⟩ :=
    cairns_geometric_initial_choice σ hσ a ha hab hacomp h p q hpq hchord
  have hstart := cairns_initial_stage_geometry hσ hacomp hab h hpq initial hchord h₁ h₂ ho₁ ho₂ hdis
  let X := {s : Stage // StageGeometry σ a h s}
  have hstep : ∀ s : X, ∃ d : StepData σ a s.val, ∀ i, StarGeometry (d.star i) h := by
    intro s
    exact cairns_stepData_of_stage_frontier σ hσ a ha hab hacomp h s.val
      s.property.isOpen s.property.connected.isPreconnected s.property.subset s.property.four s.property.chord
  choose step hgeom using hstep
  let F : X → X := fun s ↦ ⟨(step s).next h,
    cairns_successor_stage_geometry hσ hacomp hab h s.property (step s) (hgeom s)⟩
  let u : ℕ → X := fun n ↦ Nat.rec ⟨initial.stage h,hstart⟩ (fun _ s ↦ F s) n
  let d : Data σ a p q h := {
    initial := initial
    stages := fun n ↦ (u n).val
    start_eq := rfl
    steps := fun n ↦ step (u n)
    next_eq := fun n ↦ rfl }
  exact ⟨d,(fun n ↦ (u n).property),(fun n ↦ hgeom (u n))⟩

end HolomorphicAnosov.Topology.Plane

