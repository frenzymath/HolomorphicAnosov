import HolomorphicAnosov.Topology.SingularChainGeneratorIso
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u
namespace HolomorphicAnosov
/-- The coproduct comparison sends a summand to its single-coordinate generator.
Source: Hatcher, §2.1 p.108. Compare the two colimit cocones, evaluate their
factorization equation at the coefficient, then relabel using the singular-simplex
equivalence. This proves the formula also for zero coefficients and empty spaces.
DAG node: `topo.singular_subspace_chain_generator_g15`. -/
theorem singularChainGeneratorIso_hom_generator (X : TopCat.{u}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) (a : ULift.{u} ℤ) :
    (singularChainGeneratorIso X n).hom (((TopCat.toSSet.obj X).ιChainComplex
      (R := (ModuleCat.of ℤ (ULift.{u} ℤ))) σ) a) =
        Finsupp.single (X.toSSetObjEquiv _ σ) a := by
  let cc := (TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ (ULift.{u} ℤ)) n
  let ff := ModuleCat.finsuppCoconeIsColimit (R := ℤ) (M := ULift.{u} ℤ)
    ((TopCat.toSSet.obj X) _⦋n⦌)
  let i := cc.coconePointUniqueUpToIso ff
  have hcomp := cc.comp_coconePointUniqueUpToIso_hom ff ⟨σ⟩
  have hcomp' := congrArg (fun k => k.hom a) hcomp
  change i.hom (((TopCat.toSSet.obj X).ιChainComplex
    (R := (ModuleCat.of ℤ (ULift.{u} ℤ))) σ) a) = Finsupp.single σ a at hcomp'
  change ((Finsupp.mapDomain.linearEquiv (ULift.{u} ℤ) ℤ
      (X.toSSetObjEquiv (op ⦋n⦌))).toModuleIso.hom
      (i.hom (((TopCat.toSSet.obj X).ιChainComplex
        (R := (ModuleCat.of ℤ (ULift.{u} ℤ))) σ) a))) = _
  rw [hcomp']
  simp [LinearEquiv.toModuleIso, Finsupp.mapDomain.linearEquiv, Finsupp.lmapDomain_apply]

end HolomorphicAnosov
