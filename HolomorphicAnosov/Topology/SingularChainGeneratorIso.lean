import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u
namespace HolomorphicAnosov

/-- The free integral chain group comparison. Source: Hatcher, §2.1 p.108;
Mathlib's two coproduct descriptions and singular-simplex equivalence.
DAG node: `topo.singular_subspace_chain_generator_iso_g15`. -/
noncomputable def singularChainGeneratorIso (X : TopCat.{u}) (n : ℕ) :
    ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ))).X n ≅
      ModuleCat.of ℤ (C(Convexity.StdSimplex ℝ (Fin (n + 1)), X) →₀ ULift.{u} ℤ) := by
  let cc := (TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ (ULift.{u} ℤ)) n
  let ff := ModuleCat.finsuppCoconeIsColimit (R := ℤ) (M := ULift.{u} ℤ)
    ((TopCat.toSSet.obj X) _⦋n⦌)
  exact cc.coconePointUniqueUpToIso ff ≪≫
    (Finsupp.mapDomain.linearEquiv (ULift.{u} ℤ) ℤ (X.toSSetObjEquiv (op ⦋n⦌))).toModuleIso


end HolomorphicAnosov
