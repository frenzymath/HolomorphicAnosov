import HolomorphicAnosov.Topology.PathSingularSimplex

noncomputable section
open CategoryTheory
open scoped Simplicial
universe u
namespace HolomorphicAnosov.Topology

/-- Postcomposition carries a path's native singular simplex to the simplex of
the mapped path. Source: Hatcher, Algebraic Topology, p.111, induced chain map.
Both sides compose the original interval-simplex parameterization with the
continuous map, so the equality is definitional. -/
theorem pathSingularSimplex_map {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {x y : X} (α : Path x y) (g : C(X, Y)) :
    (TopCat.toSSet.map (TopCat.ofHom g)).app _ (pathSingularSimplex α) =
      pathSingularSimplex (α.map g.continuous) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of Y) _).injective
  apply ContinuousMap.ext
  intro p
  rfl
end HolomorphicAnosov.Topology
