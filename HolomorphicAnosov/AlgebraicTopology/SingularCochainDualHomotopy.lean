import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition

/-!
# Dualization of singular chain homotopies

A chain homotopy becomes a cochain homotopy after taking opposites and applying
linear Yoneda at the fixed coefficient object.  Mathlib supplies the opposite
homotopy and additive-functor transport; this module packages the combination
for the concrete singular cochain complex used by the project.
-/

open CategoryTheory CategoryTheory.Limits Opposite

universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain

/-- Dualize a homotopy of chain maps to a homotopy of the corresponding
cochain maps.  The fixed-object linear Yoneda functor is additive, even though
`linearYoneda` itself has no global additive instance.

Source: Mathlib `Algebra.Homology.Opposite` (`Homotopy.op`) and
`Algebra.Homology.Homotopy` (`Functor.mapHomotopy`); the concrete dual functor
is the one defined in `SingularCochainCohomologyDefinition`.
-/
noncomputable def dualFunctor_map_homotopy (R : Type u) [CommRing R]
    {K L : ChainComplex (ModuleCat.{u} R) ℕ} {f g : K ⟶ L}
    (h : _root_.Homotopy f g) :
    _root_.Homotopy ((dualFunctor R).map f.op) ((dualFunctor R).map g.op) := by
  let F := (CategoryTheory.linearYoneda R (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  letI : F.Additive :=
    CategoryTheory.linearYoneda_obj_additive R (ModuleCat.{u} R) (ModuleCat.of R R)
  exact F.mapHomotopy h.op

end HolomorphicAnosov.SingularCochain
