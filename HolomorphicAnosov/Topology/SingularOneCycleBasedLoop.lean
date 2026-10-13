import HolomorphicAnosov.Topology.PathSingularChain
import HolomorphicAnosov.Topology.SingularOneCycleBalancedPaths
import HolomorphicAnosov.Topology.PathListBalancedLoops
import HolomorphicAnosov.Topology.LoopListBasedBoundary

noncomputable section
open CategoryTheory
universe u
namespace HolomorphicAnosov.Topology

/-- Every native singular one-cycle in a path-connected space is homologous
to the singular chain of one loop at a prescribed basepoint.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 proof p.167. Replace the cycle
by a balanced positive list of paths, concatenate nonloop occurrences to obtain
a list of loops, and transport/concatenate them at the basepoint. Add the three
two-chain witnesses; their intermediate one-chain sums cancel. -/
theorem singularOneCycle_based_loop {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    (x : X) (a : (integralSingularChains X).X 1)
    (ha : ((integralSingularChains X).d 1 0) a = 0) :
    ∃ (α : Path x x) (c : (integralSingularChains X).X 2),
      ((integralSingularChains X).d 2 1) c = a - pathSingularChain α := by
  classical
  obtain ⟨l, c, hc, hb⟩ := singularOneCycle_balanced_paths a ha
  obtain ⟨k, d, hd⟩ := pathList_balanced_loops l hb
  obtain ⟨α, b, hα⟩ := loopList_based_boundary x k
  refine ⟨α, c + d + b, ?_⟩
  simp only [map_add, hc, hd, hα]
  abel
end HolomorphicAnosov.Topology
