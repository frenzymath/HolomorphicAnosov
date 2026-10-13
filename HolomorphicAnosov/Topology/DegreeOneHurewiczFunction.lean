import HolomorphicAnosov.Topology.LoopSingularClassHomotopic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

noncomputable section
open CategoryTheory AlgebraicTopology
open scoped Simplicial
universe u
namespace HolomorphicAnosov.Topology

/-- The explicit quotient map from the based fundamental group to singular H1.
Source: Hatcher, p. 166. The data are a quotient lift of the actual loop class. -/
def degreeOneHurewiczFunction {X : Type u} [TopologicalSpace X] (x : X) :
    FundamentalGroup X x → IntegralSingularH1 X :=
  Quotient.lift (fun α : Path x x ↦ loopSingularClass α)
    (fun _ _ h ↦ loopSingularClass_homotopic h)

end HolomorphicAnosov.Topology
