import HolomorphicAnosov.Topology.SingularHomologyExcision.Definitions

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace HolomorphicAnosov

noncomputable section

/-- Coefficient change commutes with the actual relative inclusion chain map.
Source: Hatcher arbitrary coefficients p.153; naturality of the native chain bifunctor. -/
theorem excision_coefficient_naturality
    (X : TopCat.{u}) (A B : Set X) (R Q : ModuleCat.{u} ℤ)
    (φ : R ⟶ Q) (n : ℕ) :
    SSetPair.homologyMap (singularExcisionInclusion X A B) R n ≫
        singularRelativeCoefficientMap (singularSubspacePair X A) φ n =
      singularRelativeCoefficientMap (singularExcisionSource X A B) φ n ≫
        SSetPair.homologyMap (singularExcisionInclusion X A B) Q n := by
  simp only [SSetPair.homologyMap, singularRelativeCoefficientMap,
    ← HomologicalComplex.homologyMap_comp]
  exact congrArg (fun g ↦ HomologicalComplex.homologyMap g n)
    (((SSetPair.chainComplexFunctor (ModuleCat.{u} ℤ)).map φ).naturality
      (singularExcisionInclusion X A B))


end
end HolomorphicAnosov

