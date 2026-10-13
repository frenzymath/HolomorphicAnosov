import HolomorphicAnosov.Topology.SingularHomologyExcision.Definitions
import HolomorphicAnosov.Topology.SingularHomologyExcision.QuotientDegreeIsIso

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u w
variable {K : Type w} [CommRing K]

namespace HolomorphicAnosov

noncomputable section

/-- The quotient-chain isomorphism has exactly the inclusion forward map in every degree.
Source: Hatcher excision proof p.124; the degreewise inverse above commutes with boundary
because the existing forward map is a chain map and is componentwise invertible. -/
theorem excision_quotient_iso
    (X : TopCat.{u}) (A B : Set X) (R : ModuleCat.{u} K) :
    ∃ q : (singularIntersectionPair X A B).chainComplex R ≅
        (singularExcisionSmallPair X A B).chainComplex R,
      q.hom = SSetPair.chainComplexMap (singularExcisionQuotientInclusion X A B) R := by
  let f := SSetPair.chainComplexMap (singularExcisionQuotientInclusion X A B) R
  have : ∀ n, IsIso (f.f n) := fun n ↦ excision_quotient_degree_isIso X A B R n
  have : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  exact ⟨asIso f, rfl⟩


end
end HolomorphicAnosov

