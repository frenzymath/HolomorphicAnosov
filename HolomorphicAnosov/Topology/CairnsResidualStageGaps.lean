import HolomorphicAnosov.Topology.CairnsResidualStageContacts
import HolomorphicAnosov.Topology.CairnsResidualComponentGap

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- The complementary components of a closed circle subset form a countable
family. Source: Cairns §4, recurrent Hypothesis (2), denumerability of residual
chords. Distinct components are disjoint, and local connectedness makes them
open. Each contains a point of a fixed countable dense subset of the circle,
so there are at most countably many. -/
theorem cairns_residual_components_countable (S : Set Circle) (hS : IsClosed S) :
    Set.Countable {U : Set Circle | ∃ x ∈ Sᶜ, connectedComponentIn Sᶜ x = U} := by
  apply Set.PairwiseDisjoint.countable_of_isOpen (s := fun U : Set Circle ↦ U)
  · intro U hU V hV hne
    apply Set.disjoint_left.mpr
    intro z hzU hzV
    obtain ⟨x, hx, rfl⟩ := hU
    obtain ⟨y, hy, rfl⟩ := hV
    exact hne ((connectedComponentIn_eq hzU).trans (connectedComponentIn_eq hzV).symm)
  · intro U hU
    exact residual_component_isOpen S hS ⟨U, hU⟩
  · intro U hU
    exact residual_component_nonempty S ⟨U, hU⟩

/-- Actual recurrence stages admit simultaneous proper-gap labels for their
countably many residual components. Source: Cairns §4(C), pp.864–865. The
initial chord and opposite first contacts give a closed four-point contact
set at every stage. Cutting the circle at a retained contact identifies each
complementary component with a proper exponential interval. Choose its gap
label for each component. Countability follows from openness and disjointness.
The statement also covers a completed stage, whose residual index type is empty. -/
theorem cairns_residual_stage_gap_labels
    {σ : Circle → ℂ} {a : Set ℂ} {p q : Circle} {h : (range σ) ≃ₜ Circle}
    (hσ : Topology.IsEmbedding σ) (hpq : p ≠ q) (d : Data σ a p q h) (j : ℕ) :
    Set.Countable {U : Set Circle | ∃ x ∈ ((d.stages j).contacts σ)ᶜ,
      connectedComponentIn ((d.stages j).contacts σ)ᶜ x = U} ∧
    ∃ gap : ResidualComponent ((d.stages j).contacts σ) → CairnsCircleGap,
      (∀ i, (gap i).IsGapOf ((d.stages j).contacts σ)) ∧
      (∀ i, (gap i).openArc = i.val) := by
  obtain ⟨hclosed, hfour⟩ := cairns_residual_stage_contacts_four hσ hpq d j
  refine ⟨cairns_residual_components_countable _ hclosed, ?_⟩
  choose gap hgap harc using cairns_gap_of_residual_component _ hclosed hfour
  exact ⟨gap, hgap, harc⟩

end HolomorphicAnosov.Topology.Plane
