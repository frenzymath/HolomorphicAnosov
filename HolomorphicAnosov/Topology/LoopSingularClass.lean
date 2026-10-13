import HolomorphicAnosov.Topology.IntegralSingularH1
import HolomorphicAnosov.Topology.LoopSingularChainIsCycle
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

noncomputable section
open CategoryTheory AlgebraicTopology
open scoped Simplicial
universe u
namespace HolomorphicAnosov.Topology

/-- The loop cycle projected to native ordinary singular homology.
Source: Hatcher, p. 166. Only its cycle proof is postponed; the cycle
data, kernel-to-native-cycles isomorphism, and quotient projection are explicit. -/
def loopSingularClass {X : Type u} [TopologicalSpace X] {x : X} (α : Path x x) :
    IntegralSingularH1 X :=
  (integralSingularChains X).homologyπ 1
    (((integralSingularChains X).sc 1).moduleCatCyclesIso.inv
      ⟨pathSingularChain α, loopSingularChain_isCycle α⟩)

end HolomorphicAnosov.Topology
