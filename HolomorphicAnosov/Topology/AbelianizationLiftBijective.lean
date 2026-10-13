import Mathlib.GroupTheory.Abelianization.Defs

namespace HolomorphicAnosov.Topology
universe u v
/-- A surjective homomorphism to an abelian group with commutator kernel induces
a bijective canonical map from the abelianization.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 p.167. Surjectivity descends
along the quotient projection. The quotient lift is injective exactly when
the original kernel is contained in the quotient subgroup. -/
theorem abelianization_lift_bijective
    {G : Type u} [Group G] {A : Type v} [CommGroup A] (f : G →* A)
    (hs : Function.Surjective f) (hk : f.ker = commutator G) :
    Function.Bijective (Abelianization.lift f) := by
  constructor
  · exact (QuotientGroup.injective_lift_iff _ f (Abelianization.commutator_subset_ker f)).2
      (by rw [hk])
  · intro a
    obtain ⟨g, hg⟩ := hs a
    exact ⟨Abelianization.of g, (Abelianization.lift_apply_of f g).trans hg⟩
end HolomorphicAnosov.Topology
