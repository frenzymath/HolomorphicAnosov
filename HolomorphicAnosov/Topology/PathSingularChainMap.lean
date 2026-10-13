import HolomorphicAnosov.Topology.PathSingularChain
import HolomorphicAnosov.Topology.PathSingularSimplexMap

noncomputable section
open CategoryTheory AlgebraicTopology
universe u
namespace HolomorphicAnosov.Topology

/-- The native singular chain map sends a path generator to the mapped path
generator. Source: Hatcher, Algebraic Topology, p.111. Apply the coproduct-generator
chain-map formula and the original singular-simplex postcomposition identity. -/
theorem pathSingularChain_map {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {x y : X} (α : Path x y) (g : C(X, Y)) :
    ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom g))
      (ModuleCat.of ℤ (ULift.{u} ℤ))).f 1) (pathSingularChain α) =
      pathSingularChain (α.map g.continuous) := by
  have h := congrArg (fun f ↦ f.hom (1 : ModuleCat.of ℤ (ULift.{u} ℤ)))
    (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of X)) (TopCat.toSSet.obj (TopCat.of Y)) (TopCat.toSSet.map (TopCat.ofHom g))
      (ModuleCat.of ℤ (ULift.{u} ℤ)) (pathSingularSimplex α))
  simpa only [pathSingularSimplex_map, ModuleCat.hom_comp, LinearMap.comp_apply,
    pathSingularChain] using h
end HolomorphicAnosov.Topology
