import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition
import HolomorphicAnosov.AlgebraicTopology.SingularCochainDualHomotopy
open CategoryTheory CategoryTheory.Limits Opposite
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain
set_option backward.isDefEq.respectTransparency false
/-- Source: Hatcher, Algebraic Topology, pp.201–202.

Dualize the two homotopies of the chain equivalence by taking their opposites and applying linear Yoneda. The order of hom and inv is reversed, yielding a cochain homotopy equivalence. Its homology map is an isomorphism by the homotopy invariance of homology. Conjugating this map by the canonical module homology quotient isomorphisms gives the explicit quotientMap, which is therefore an isomorphism. -/
theorem dual_homotopy_equivalence_isIso (R : Type u) [CommRing R]
    {C D : ChainComplex (ModuleCat.{u} R) ℕ} (e : HomotopyEquiv C D) (n : ℕ) :
    IsIso (quotientMap R ((dualFunctor R).map e.hom.op) n) := by
  let de : HomotopyEquiv ((dualFunctor R).obj (op D)) ((dualFunctor R).obj (op C)) :=
    { hom := (dualFunctor R).map e.hom.op
      inv := (dualFunctor R).map e.inv.op
      homotopyHomInvId := dualFunctor_map_homotopy R e.homotopyInvHomId
      homotopyInvHomId := dualFunctor_map_homotopy R e.homotopyHomInvId }
  have : IsIso (HomologicalComplex.homologyMap de.hom n) :=
    (de.toHomologyIso n).isIso_hom
  change IsIso (quotientMap R de.hom n)
  unfold quotientMap
  infer_instance
end HolomorphicAnosov.SingularCochain

