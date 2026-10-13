import HolomorphicAnosov.Topology.IntegralSingularChains
import HolomorphicAnosov.Topology.PathSingularSimplex

noncomputable section
open CategoryTheory AlgebraicTopology
open scoped Simplicial
universe u
namespace HolomorphicAnosov.Topology

/-- The finite integral singular chain with coefficient one on the path simplex.
Source: Hatcher, pp. 108–109 and 166; this is the native coproduct generator. -/
def pathSingularChain {X : Type u} [TopologicalSpace X] {a b : X} (α : Path a b) :
    (integralSingularChains X).X 1 :=
  ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
    (R := ModuleCat.of ℤ (ULift.{u} ℤ)) (pathSingularSimplex α)).hom 1

end HolomorphicAnosov.Topology

