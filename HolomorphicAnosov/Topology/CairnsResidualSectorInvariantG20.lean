import HolomorphicAnosov.Topology.CairnsResidualSectorInvariant

namespace HolomorphicAnosov.Topology.Plane

open Set CairnsStar CairnsRefinement

/-- The recurrence-stage residual-sector invariant under the G20 public name.
Source: Cairns (1951), §4(C), pp.864–865. Apply the corrected invariant to the
same recurrence, index and successor inclusion; all witnesses and properties
are preserved. The former arbitrary-stage statement had the empty-contact
counterexample recorded in `CairnsResidualSectorInvariant`.
DAG node: topo.cairns_residual_sector_invariant_g20. -/
theorem cairns_residual_sector_invariant_g20
    {σ : Circle → ℂ} {a : Set ℂ} {p q : Circle} {h : (range σ) ≃ₜ Circle}
    (d : Data σ a p q h) (j : ℕ) (hnext : (d.stages (j + 1)).region ⊆ a)
    (_hAdapter : True) :
    ∀ i : ResidualComponent ((d.stages j).contacts σ),
      ∃ (g : CairnsCircleGap) (α' : I → Circle) (β : Set ℂ),
        g.IsGapOf ((d.stages j).contacts σ) ∧ g.openArc = i.val ∧
        Topology.IsEmbedding α' ∧
        α' ⟨0, by simp⟩ = g.first ∧ α' ⟨1, by simp⟩ = g.last ∧
        range g.parameter ∪ range α' = univ ∧
        range g.parameter ∩ range α' = {g.first, g.last} ∧
        openSegment ℝ (σ g.first) (σ g.last) ⊆ a ∧
        (∃ x ∈ a \ openSegment ℝ (σ g.first) (σ g.last),
          connectedComponentIn (a \ openSegment ℝ (σ g.first) (σ g.last)) x = β) ∧
        frontier β ⊆ segment ℝ (σ g.first) (σ g.last) ∪ σ '' g.closedArc ∧
        Disjoint β (d.stages j).region := by
  exact cairns_residual_sector_invariant d j hnext

end HolomorphicAnosov.Topology.Plane
