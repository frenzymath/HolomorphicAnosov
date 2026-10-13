import HolomorphicAnosov.Topology.PathSingularSimplex

noncomputable section
open CategoryTheory
open scoped Simplicial
universe u
namespace HolomorphicAnosov.Topology

/-- The original singular simplex determines a path with fixed endpoints
uniquely. Source: Hatcher, Algebraic Topology, pp.166–167, identifying paths
with parametrized singular edges. Apply the interval-simplex equivalence to
the equality and then use extensionality of bundled paths. In particular,
independent based-loop extractions from paired equal edges agree literally. -/
theorem pathSingularSimplex_injective {X : Type u} [TopologicalSpace X]
    (x y : X) : Function.Injective (pathSingularSimplex (a := x) (b := y)) := by
  intro α β h
  have h' := congrArg (TopCat.toSSetObj₁Equiv (X := TopCat.of X)) h
  simp only [pathSingularSimplex, Equiv.apply_symm_apply] at h'
  apply (TopCat.pathEquiv (X := TopCat.of X)).symm.injective
  ext t
  exact congrArg (fun f ↦ f t) h'

end HolomorphicAnosov.Topology
