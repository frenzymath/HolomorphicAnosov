import HolomorphicAnosov.Topology.IntegralSingularChains

noncomputable section
open CategoryTheory AlgebraicTopology
open scoped Simplicial
universe u
namespace HolomorphicAnosov.Topology

/-- The additive module of ordinary integral singular homology in degree one.
Source: Hatcher, p. 108; this is the native homology object of the above complex. -/
abbrev IntegralSingularH1 (X : Type u) [TopologicalSpace X] : Type u :=
  (integralSingularChains X).homology 1

end HolomorphicAnosov.Topology

