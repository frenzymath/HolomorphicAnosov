import HolomorphicAnosov.Topology.SingularExcisionPairComparison
import HolomorphicAnosov.Topology.SingularHomologyExcision.Definitions
import HolomorphicAnosov.Topology.SingularHomologyExcision.QuotientIso

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u w
variable {K : Type w} [CommRing K]

namespace HolomorphicAnosov

noncomputable section

/-- Transport the genuine small relative equivalence to the original topological pair.
Source: Hatcher p.124; the published subspace adapter identifies both pair components and
its exact inclusion square. This is a deduction from a constructed small equivalence,
not an extra hypothesis of the public excision theorem. -/
theorem excision_source_equiv_of_small
    (X : TopCat.{u}) (A B : Set X) (R : ModuleCat.{u} K)
    (small : HomotopyEquiv ((singularExcisionSmallPair X A B).chainComplex R)
      ((singularSubspace X A).pair.chainComplex R))
    (hsmall : small.hom = SSetPair.chainComplexMap (singularExcisionSmallInclusion X A B) R) :
    ∃ e : HomotopyEquiv ((singularExcisionSource X A B).chainComplex R)
        ((singularSubspacePair X A).chainComplex R),
      e.hom = SSetPair.chainComplexMap (singularExcisionInclusion X A B) R := by
  obtain ⟨ep, ei, hei⟩ := singular_excision_pair_comparison X A B
  obtain ⟨q, hq⟩ := excision_quotient_iso X A B R
  let F := (SSetPair.chainComplexFunctor (ModuleCat.{u} K)).obj R
  let e := ((HomotopyEquiv.ofIso (F.mapIso ei)).trans
    ((HomotopyEquiv.ofIso q).trans small)).trans
      (HomotopyEquiv.ofIso (F.mapIso ep.symm))
  refine ⟨e, ?_⟩
  change ((F.map ei.hom) ≫ q.hom ≫ small.hom) ≫
    F.map ep.inv = _
  rw [hq, hsmall]
  have hcomp : singularExcisionQuotientInclusion X A B ≫
      singularExcisionSmallInclusion X A B = singularIntersectionInclusion X A B := by
    apply MorphismProperty.Arrow.Hom.ext <;> rfl
  change (F.map ei.hom ≫
    F.map (singularExcisionQuotientInclusion X A B) ≫
    F.map (singularExcisionSmallInclusion X A B)) ≫ F.map ep.inv = _
  rw [← F.map_comp, hcomp, ← F.map_comp, hei, F.map_comp]
  simp only [Category.assoc, ← F.map_comp, Iso.hom_inv_id, Category.comp_id]
  rfl


end
end HolomorphicAnosov

