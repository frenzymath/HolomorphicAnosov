import HolomorphicAnosov.Topology.SingularChainGenerator
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u
namespace HolomorphicAnosov
/-- The free-chain comparison respects the alternating face boundary.
Source: Hatcher, §2.1 p.108. Evaluate Mathlib's summand differential equation at
the coefficient, apply the comparison, distribute over the finite sum, and use
the generator formula for every face.
DAG node: `topo.singular_subspace_chain_boundary_g15`. -/
theorem singularChainGeneratorIso_hom_boundary (X : TopCat.{u}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋n + 1⦌) (a : ULift.{u} ℤ) :
    (singularChainGeneratorIso X n).hom (((TopCat.toSSet.obj X).chainComplex
      (ModuleCat.of ℤ (ULift.{u} ℤ))).d (n + 1) n
      (((TopCat.toSSet.obj X).ιChainComplex
        (R := (ModuleCat.of ℤ (ULift.{u} ℤ))) σ) a)) =
      ∑ i : Fin (n + 2),
        (-1 : ℤ) ^ i.val • Finsupp.single
          (X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i σ)) a := by
  have hd := SSet.ιChainComplex_d (X := TopCat.toSSet.obj X)
    (R := (ModuleCat.of ℤ (ULift.{u} ℤ))) σ
  have hd' := congrArg (fun k =>
    (singularChainGeneratorIso X n).hom
      (k.hom a)) hd
  simp only [CategoryTheory.comp_apply] at hd'
  simp only [ModuleCat.hom_sum, ModuleCat.hom_smul] at hd'
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul] at hd'
  refine hd'.trans ?_
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  exact singularChainGeneratorIso_hom_generator X n _ a


end HolomorphicAnosov
