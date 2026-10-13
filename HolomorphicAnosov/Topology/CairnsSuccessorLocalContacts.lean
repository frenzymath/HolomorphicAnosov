import HolomorphicAnosov.Topology.CairnsSuccessorClosure
import HolomorphicAnosov.Topology.CairnsSuccessorCompactness
import HolomorphicAnosov.Topology.CairnsGeometricStarChoice
import HolomorphicAnosov.Topology.CairnsGapHullSeparation

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- On each old closed gap arc, the successor contacts are exactly the
contacts of that gap's newly attached front. Old contacts on the arc are its
two endpoints. Contacts from any other new star belong to the other closed
arc, so disjointness of the gap interiors again forces the common point to be
an old endpoint. Source: Cairns §4(C), refinement of complementary arcs. -/
theorem cairns_successor_contacts_on_gap
    {σ : Circle → ℂ} {a : Set ℂ} {s : Stage}
    (hσ : Topology.IsEmbedding σ) (d : StepData σ a s) (h : range σ ≃ₜ Circle)
    (hgeo : ∀ i, StarGeometry (d.star i) h)
    (hT : (d.next h).contacts σ = s.contacts σ ∪
      ⋃ i, σ ⁻¹' ((d.star i).front ∩ range σ)) :
    ∀ i t, t ∈ (d.gap i).closedArc →
      (t ∈ (d.next h).contacts σ ↔ σ t ∈ (d.star i).front ∩ range σ) := by
  have hlocal : ∀ i, σ ⁻¹' ((d.star i).front ∩ range σ) ⊆ (d.gap i).closedArc := by
    intro i t ht
    have hsub : (d.star i).front ∩ range σ ⊆ σ '' range (d.gap i).parameter :=
      (hgeo i).2.2.2.2.2.2.2.2.2.1
    obtain ⟨u,hu,he⟩ := hsub ht
    have hut := hσ.injective he
    rw [← hut,← (CairnsCircleGap.parameter_embedding_range (d.gap i)).2.1]
    exact hu
  intro i t ht
  have hends : t = (d.gap i).first ∨ t = (d.gap i).last →
      σ t ∈ (d.star i).front ∩ range σ := by
    rintro (rfl | rfl)
    · exact (hgeo i).2.2.2.2.2.2.2.2.2.2.1
    · exact (hgeo i).2.2.2.2.2.2.2.2.2.2.2.1
  rw [hT]
  constructor
  · rintro (htold | htnew)
    · apply hends
      rcases (d.gap i).closedArc_subset_openArc_union_endpoints ht with htopen | htend
      · obtain ⟨x,hx,hcomp⟩ := (d.gap_isGap i).2.2
        exact (connectedComponentIn_subset (s.contacts σ)ᶜ x (hcomp.symm ▸ htopen) htold).elim
      · exact htend
    · obtain ⟨j,hj⟩ := mem_iUnion.mp htnew
      by_cases hji : j = i
      · subst j
        exact hj
      · apply hends
        rcases (d.gap i).closedArc_subset_openArc_union_endpoints ht with htopen | htend
        · exact (cairns_disjoint_gap_closedArc_subset_complement (s.contacts σ)
            (d.gap i) (d.gap j) (d.gap_isGap i) (d.gap_isGap j)
            (cairns_step_gap_pairwise_disjoint d (Ne.symm hji)) (hlocal j hj) htopen).elim
        · exact htend
  · intro htstar
    exact Or.inr (mem_iUnion.mpr ⟨i,htstar⟩)

end HolomorphicAnosov.Topology.Plane

