import HolomorphicAnosov.Topology.SingularHomologyExcision

/-! # Support-neighborhood excision with module coefficients

Source: Hatcher, *Algebraic Topology*, excision p.124, coefficients p.153,
and the chart comparison in Lemma 3.27, p.237.
-/

open CategoryTheory Set

namespace HolomorphicAnosov

universe u v

/-- An open neighborhood containing the closure of a support induces the
canonical isomorphism on relative singular homology, over any commutative
coefficient ring and in every natural degree.

Source: Hatcher, *Algebraic Topology*, pp.124 and153, applied to the support
pairs of Lemma 3.27, p.237. Proof: the interiors of the support complement
and its open neighborhood cover the space. The barycentric subdivision
construction gives the relative small-chain homotopy equivalence for these
same coefficients. The native intersection-pair comparison transports it
to the original subspace pair with the exact inclusion as forward map.
Taking homology of this chain homotopy equivalence proves that the canonical
inclusion map is an isomorphism, including degree zero. -/
theorem support_neighborhood_excision_isIso_coefficients
    {R : Type v} [CommRing R] (X : TopCat.{u}) (K U : Set X)
    (hU : IsOpen U) (hKU : closure K ⊆ U)
    (V : ModuleCat.{u} R) (q : ℕ) :
    IsIso (SSetPair.homologyMap (singularExcisionInclusion X Kᶜ U) V q) := by
  have hcover : interior Kᶜ ∪ interior U = univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ closure K
    · exact Or.inr ((subset_interior_iff_isOpen.mpr hU) (hKU hx))
    · exact Or.inl (by rwa [interior_compl])
  obtain ⟨e, he⟩ := excision_source_equiv_of_small X Kᶜ U V
    (NativeBarycentricOperators.smallRelativeHomotopyEquiv.{u, u} X Kᶜ U hcover V) rfl
  have hm : (e.toHomologyIso q).hom =
      SSetPair.homologyMap (singularExcisionInclusion X Kᶜ U) V q := by
    change HomologicalComplex.homologyMap e.hom q = _
    rw [he]
  rw [← hm]
  infer_instance

end HolomorphicAnosov

