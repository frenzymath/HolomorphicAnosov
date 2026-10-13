import HolomorphicAnosov.Topology.SingularChainGenerator
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u
namespace HolomorphicAnosov
/-- Continuous maps act by postcomposition on the compared chain generators.
Source: Hatcher, §2.1 pp.110–111. Evaluate the simplicial chain-map equation at
the coefficient, apply the comparison, and use that the singular functor acts by
postcomposition, as seen by evaluating both continuous maps on simplex points.
DAG node: `topo.singular_subspace_chain_map_generator_g15`. -/
theorem singularChainGeneratorIso_hom_map_generator {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) (a : ULift.{u} ℤ) :
    (singularChainGeneratorIso Y n).hom
      ((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℤ (ULift.{u} ℤ))).f n
        (((TopCat.toSSet.obj X).ιChainComplex
          (R := (ModuleCat.of ℤ (ULift.{u} ℤ))) σ) a)) =
      Finsupp.single (f.hom.comp (X.toSSetObjEquiv _ σ)) a := by
  have hm := SSet.ι_chainComplexMap_f (X := TopCat.toSSet.obj X)
    (Y := TopCat.toSSet.obj Y) (f := TopCat.toSSet.map f)
    (R := (ModuleCat.of ℤ (ULift.{u} ℤ))) σ
  have hm' := congrArg (fun k => (singularChainGeneratorIso Y n).hom (k.hom a)) hm
  simp only [CategoryTheory.comp_apply] at hm'
  rw [singularChainGeneratorIso_hom_generator] at hm'
  convert hm' using 1
  ext z
  rfl

end HolomorphicAnosov
