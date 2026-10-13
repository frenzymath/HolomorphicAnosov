import HolomorphicAnosov.Topology.PathSingularChain
import HolomorphicAnosov.Topology.SingularOneChainPositivePaths
import HolomorphicAnosov.Topology.PathListCycleEndpointBalance

noncomputable section
open CategoryTheory
universe u
namespace HolomorphicAnosov.Topology

/-- Every native integral singular one-cycle is homologous to a positive path
list balanced at each endpoint.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 proof p.167. Replace the cycle
by its positive path representative. Their difference is a boundary, so its
boundary is zero; hence the new representative is still a cycle. The native
boundary coefficient calculation gives equal incoming and outgoing counts. -/
theorem singularOneCycle_balanced_paths {X : Type u} [TopologicalSpace X]
    [DecidableEq X] (a : (integralSingularChains X).X 1)
    (ha : ((integralSingularChains X).d 1 0) a = 0) :
    ∃ (l : List (Σ x y : X, Path x y)) (c : (integralSingularChains X).X 2),
      ((integralSingularChains X).d 2 1) c = a -
        (l.map (fun p ↦ pathSingularChain p.2.2)).sum ∧
      ∀ v, (l.map (fun p ↦ p.1)).count v = (l.map (fun p ↦ p.2.1)).count v := by
  obtain ⟨l, c, hc⟩ := singularOneChain_positive_paths a
  refine ⟨l, c, hc, ?_⟩
  apply pathList_cycle_endpoint_balance l
  have hd := congrArg (fun f ↦ f c) ((integralSingularChains X).d_comp_d 2 1 0)
  change ((integralSingularChains X).d 1 0) (((integralSingularChains X).d 2 1) c) = 0 at hd
  rw [hc, map_sub, ha, zero_sub, neg_eq_zero] at hd
  exact hd
end HolomorphicAnosov.Topology
