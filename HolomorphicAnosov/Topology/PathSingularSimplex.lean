import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy

noncomputable section
open CategoryTheory
open scoped Simplicial
universe u
namespace HolomorphicAnosov.Topology

/-- A path's original singular one-simplex, in the actual singular simplicial set.
Source: Hatcher, p. 166; Mathlib's equivalence respects the endpoint face order. -/
def pathSingularSimplex {X : Type u} [TopologicalSpace X] {a b : X} (α : Path a b) :
    (TopCat.toSSet.obj (TopCat.of X)) _⦋1⦌ :=
  TopCat.toSSetObj₁Equiv.symm (TopCat.pathEquiv.symm α).hom

end HolomorphicAnosov.Topology

