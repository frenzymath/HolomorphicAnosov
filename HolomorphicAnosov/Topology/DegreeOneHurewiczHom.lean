import HolomorphicAnosov.Topology.DegreeOneHurewiczFunctionLaws
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Algebra.Group.TypeTags.Hom

noncomputable section
open CategoryTheory AlgebraicTopology
open scoped Simplicial
universe u
namespace HolomorphicAnosov.Topology

/-- The integral Hurewicz homomorphism, with a type tag for its additive codomain.
Source: Hatcher, p. 166. Its function is the concrete quotient lift above. -/
def degreeOneHurewicz {X : Type u} [TopologicalSpace X] (x : X) :
    FundamentalGroup X x →* Multiplicative (IntegralSingularH1 X) where
  toFun a := Multiplicative.ofAdd (degreeOneHurewiczFunction x a)
  map_one' := congrArg Multiplicative.ofAdd (degreeOneHurewiczFunction_laws x).1
  map_mul' a b := congrArg Multiplicative.ofAdd ((degreeOneHurewiczFunction_laws x).2 a b)

end HolomorphicAnosov.Topology
