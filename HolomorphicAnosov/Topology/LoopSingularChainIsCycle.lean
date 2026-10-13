import HolomorphicAnosov.Topology.PathSingularChain
import HolomorphicAnosov.Topology.SimplicialOneSimplexCycle

noncomputable section
open CategoryTheory AlgebraicTopology
open scoped Simplicial
universe u
namespace HolomorphicAnosov.Topology

/-- A based loop is an actual degree-one cycle.

Source and proof: Hatcher, Theorem 2A.1, p. 166. The alternating face
differential of a one-simplex is its zeroth face minus its first face.
The interval equivalence identifies these with the endpoint and starting
point, respectively. Both endpoints of a based loop are the same point,
so the two native integer-one generators cancel. This is membership in
the actual kernel of the native differential, not a supplied cycle. -/
theorem loopSingularChain_isCycle {X : Type u} [TopologicalSpace X]
    {x : X} (α : Path x x) :
    pathSingularChain α ∈ LinearMap.ker ((integralSingularChains X).sc 1).g.hom  := by
  refine simplicial_one_simplex_isCycle (TopCat.toSSet.obj (TopCat.of X))
    (ModuleCat.of ℤ (ULift.{u} ℤ)) (pathSingularSimplex α) ?_ 1
  simp only [pathSingularSimplex, TopCat.δ_zero_toSSetObj₁Equiv.symm,
    TopCat.δ_one_toSSetObj₁Equiv.symm]
  exact congrArg TopCat.toSSetObj₀Equiv.symm
    (((TopCat.pathEquiv (X := TopCat.of X)).symm α).hom₁.trans
      ((TopCat.pathEquiv (X := TopCat.of X)).symm α).hom₀.symm)

end HolomorphicAnosov.Topology

