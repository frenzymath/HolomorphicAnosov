import HolomorphicAnosov.Topology.SingularHomologyExcision.Definitions

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u w
variable {K : Type w} [CommRing K]

namespace HolomorphicAnosov

noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- The exact relative chain projection is natural in every pair map.
Source: native `chainComplexFunctorπ`; this is the quotient map used by Hatcher p.118. -/
theorem pair_projection_naturality {P Q : SSetPair.{u}}
    (f : P ⟶ Q) (R : ModuleCat.{u} K) (n : ℕ) :
    (P.chainComplexπ R).f n ≫ (SSetPair.chainComplexMap f R).f n =
      (SSet.chainComplexMap f.hom.right R).f n ≫ (Q.chainComplexπ R).f n := by
  simpa [SSetPair.chainComplexFunctorRight, SSetPair.chainComplexπ,
    SSetPair.chainComplexMap, SSet.chainComplexMap, HomologicalComplex.comp_f] using
    (congrArg (fun g ↦ g.f n)
      ((((SSetPair.chainComplexFunctorπ (ModuleCat.{u} K)).app R).naturality f))).symm


end
end HolomorphicAnosov

