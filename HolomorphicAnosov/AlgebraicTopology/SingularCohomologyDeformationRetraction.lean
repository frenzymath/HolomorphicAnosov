import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition
import HolomorphicAnosov.AlgebraicTopology.CochainDualHomotopyEquivalence
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Algebra.Homology.Homotopy

/-!
# Absolute cohomology invariance of a deformation retraction

Source: Hatcher, Algebraic Topology, homotopy invariance p.201, with the singular
chain prism on pp.112–113. No relative pair theorem or excision is used.
DAG: topo.singular_cohomology_deformation_retraction_g5.
-/
open CategoryTheory CategoryTheory.Limits Opposite
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain

/-- The actual absolute cohomology pullback of a deformation-retract inclusion
is an isomorphism over any commutative ring, in every nonnegative degree.

Proof: apply singular chains to inclusion and retraction. Their first composite
is the identity by functoriality. The supplied topological deformation, reversed,
gives the other chain-homotopy inverse identity by the singular prism. Dualize
this chain homotopy equivalence and pass to the canonical cocycle quotients. -/
theorem cohomologyPullback_isIso_of_deformationRetraction
    (R : Type u) [CommRing R] {A U : TopCat.{u}} (i : A ⟶ U) (r : U ⟶ A)
    (hri : i ≫ r = 𝟙 A) (H : TopCat.Homotopy (𝟙 U) (r ≫ i)) (n : ℕ) :
    IsIso (cohomologyPullback R i n) := by
  let e : HomotopyEquiv ((chainFunctor R).obj A) ((chainFunctor R).obj U) :=
    { hom := (chainFunctor R).map i
      inv := (chainFunctor R).map r
      homotopyHomInvId := _root_.Homotopy.ofEq (by
        rw [← CategoryTheory.Functor.map_comp, hri, CategoryTheory.Functor.map_id])
      homotopyInvHomId := by
        let Hrev : TopCat.Homotopy (r ≫ i) (𝟙 U) := H.symm
        have h := Hrev.singularChainComplexFunctorObjMap (ModuleCat.of R R)
        simpa only [← CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using h }
  exact dual_homotopy_equivalence_isIso R e n

end HolomorphicAnosov.SingularCochain
