import HolomorphicAnosov.Topology.SingularHomologyExcision

open CategoryTheory

namespace HolomorphicAnosov

/-- Any subset containing an interior neighborhood of a closed point induces the
canonical isomorphism on point-relative singular homology. The subset need not
be open: its interior and the open punctured space cover the ambient space.
Apply Hatcher's excision theorem in the interiors-cover form, Theorem 2.20
pp.119–124. This applies in every degree and for any integer-module coefficients. -/
theorem point_neighborhood_excision_isIso
    (X : TopCat.{u}) [T1Space X] (x : X) (B : Set X)
    (hx : x ∈ interior B) (R : ModuleCat.{u} ℤ) (q : ℕ) :
    IsIso (SSetPair.homologyMap (singularExcisionInclusion X ({x} : Set X)ᶜ B) R q) := by
  have hcover : interior ({x} : Set X)ᶜ ∪ interior B = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    by_cases hy : y = x
    · subst y
      exact Or.inr hx
    · apply Or.inl
      rw [isClosed_singleton.isOpen_compl.interior_eq]
      exact hy
  exact (singular_homology_excision_barycentric_subdivision.2.1 X ({x} : Set X)ᶜ
    B hcover R).2.2 q

end HolomorphicAnosov

