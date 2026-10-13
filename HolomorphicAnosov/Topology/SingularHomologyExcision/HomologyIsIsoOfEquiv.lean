import HolomorphicAnosov.Topology.SingularHomologyExcision.Definitions

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace HolomorphicAnosov

noncomputable section

/-- Native homology of a chain homotopy equivalence preserves its exact forward map.
Source: Hatcher p.124 and native `HomotopyEquiv.toHomologyIso`, including degree zero. -/
theorem excision_homology_isIso_of_equiv
    (X : TopCat.{u}) (A B : Set X) (R : ModuleCat.{u} ℤ)
    (e : HomotopyEquiv ((singularExcisionSource X A B).chainComplex R)
      ((singularSubspacePair X A).chainComplex R))
    (he : e.hom = SSetPair.chainComplexMap (singularExcisionInclusion X A B) R)
    (n : ℕ) : IsIso (SSetPair.homologyMap (singularExcisionInclusion X A B) R n) := by
  have hh : (e.toHomologyIso n).hom =
      SSetPair.homologyMap (singularExcisionInclusion X A B) R n := by
    change HomologicalComplex.homologyMap e.hom n = _
    rw [he]
  rw [← hh]
  infer_instance


end
end HolomorphicAnosov

