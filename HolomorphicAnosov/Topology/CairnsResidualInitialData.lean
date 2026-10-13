import HolomorphicAnosov.Topology.CairnsResidualStarRefinement
import HolomorphicAnosov.Topology.CairnsInitialStarChoice

namespace HolomorphicAnosov.Topology.Plane

open Set CairnsStar CairnsRefinement

/-!
# Cairns initial two-star datum

Source: Cairns (1951), §3(D,E) and §4(A), printed pp.862–864.  The prescribed
chord determines the two opposite angular gaps and their first-contact source
stars; the resulting pair is the initial datum for the recurrent construction.
The simultaneous first-contact and star existence argument is retained as this
named source obligation so it is not hidden in the later countable recurrence.

DAG node: topo.cairns_residual_initial_data_g20.
-/
theorem cairns_residual_initial_data_source_obligation
    (σ : Circle → ℂ) (hσ : Topology.IsEmbedding σ)
    (a : Set ℂ) (ha : a.Nonempty) (haBounded : Bornology.IsBounded a)
    (haComponent : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (_h : (range σ) ≃ₜ Circle) (p q : Circle) (hpq : p ≠ q)
    (hChord : openSegment ℝ (σ p) (σ q) ⊆ a) (_hInitial : True) :
    ∃ d : InitialData σ a p q,
      d.firstGap.first = p ∧ d.firstGap.last = q := by
  exact cairns_initial_star_choice_source_obligation σ hσ a ha haBounded
    haComponent p q hpq hChord trivial

end HolomorphicAnosov.Topology.Plane
