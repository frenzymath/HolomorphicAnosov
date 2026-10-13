import HolomorphicAnosov.Topology.SingularHomologyExcision.Definitions

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace HolomorphicAnosov

noncomputable section

/-- The closure/interior version has the same interiors cover, with no separation axiom.
Source: Hatcher Theorem 2.20 p.119; native complement identities for closure and interior. -/
theorem excision_complement_cover
    (X : TopCat.{u}) (A Z : Set X) (hZ : closure Z ⊆ interior A) :
    interior A ∪ interior Zᶜ = Set.univ := by
  rw [interior_compl]
  ext x
  simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_univ, iff_true]
  by_cases hx : x ∈ closure Z
  · exact Or.inl (hZ hx)
  · exact Or.inr hx


end
end HolomorphicAnosov

