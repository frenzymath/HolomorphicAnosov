import HolomorphicAnosov.Topology.GallierXuIntervalLinkChain

noncomputable section
open Set Topology _root_.Topology
namespace HolomorphicAnosov.Topology.GallierXu

/-- A path edge in the interval presentation of a vertex link is an actual
simplicial link edge, hence comes from an original triangle containing that vertex. -/
lemma pathEdge_surfaceLink_triangle {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (v : Fin N)
    (l : List (Fin N))
    (hpath : ∀ a b, linkEdge K v a b ↔ pathEdge l a b)
    {a b : Fin N} (hab : pathEdge l a b) :
    linkEdge K v a b ∧ ({v, a, b} : Finset (Fin N)) ∈ K.faces := by
  have hlink : linkEdge K v a b := (hpath a b).2 hab
  exact ⟨hlink, hlink.2.2.2⟩

/-- Every interval-link path edge contains the original edge from the link vertex
and either endpoint. -/
lemma pathEdge_surfaceLink_edge_subset {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (v : Fin N)
    (l : List (Fin N))
    (hpath : ∀ a b, linkEdge K v a b ↔ pathEdge l a b)
    {a b : Fin N} (hab : pathEdge l a b) :
    ({v, a} : Finset (Fin N)) ∈ K.faces := by
  have htri : ({v, a, b} : Finset (Fin N)) ∈ K.faces :=
    (pathEdge_surfaceLink_triangle K v l hpath hab).2
  refine (K.isRelLowerSet_faces htri).2 ?_ ?_
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
    rcases hz with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · exact ⟨v, by simp⟩

end HolomorphicAnosov.Topology.GallierXu

namespace HolomorphicAnosov.Topology.GallierXu

/-- SurfaceLinks transports every interval-list path chain to a chain of actual
simplicial link edges at the same vertex. -/
lemma pathEdge_eqvGen_to_linkEdge {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (v : Fin N)
    (l : List (Fin N))
    (hpath : ∀ a b, linkEdge K v a b ↔ pathEdge l a b)
    {a b : Fin N} :
    Relation.EqvGen (pathEdge l) a b → Relation.EqvGen (linkEdge K v) a b := by
  intro hab
  induction hab with
  | rel x y hxy =>
      exact Relation.EqvGen.rel _ _ ((hpath x y).2 hxy)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y hxy ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact Relation.EqvGen.trans _ _ _ ihxy ihyz

end HolomorphicAnosov.Topology.GallierXu

namespace HolomorphicAnosov.Topology.GallierXu

/-- Both original edges incident to the link vertex are faces of every incident
simplicial triangle. -/
lemma linkEdge_edge_faces {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (v a b : Fin N)
    (hlink : linkEdge K v a b) :
    ({v, a} : Finset (Fin N)) ∈ K.faces ∧
      ({v, b} : Finset (Fin N)) ∈ K.faces := by
  have htri : ({v, a, b} : Finset (Fin N)) ∈ K.faces := hlink.2.2.2
  constructor
  · refine (K.isRelLowerSet_faces htri).2 ?_ ?_
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
      rcases hz with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · exact ⟨v, by simp⟩
  · refine (K.isRelLowerSet_faces htri).2 ?_ ?_
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
      rcases hz with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)
    · exact ⟨v, by simp⟩

end HolomorphicAnosov.Topology.GallierXu
