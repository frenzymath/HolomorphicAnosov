import HolomorphicAnosov.Topology.PathSingularChain
import HolomorphicAnosov.Topology.LoopSingularClassEqZero
import HolomorphicAnosov.Topology.PathTransSingularBoundary
import HolomorphicAnosov.Topology.LoopSingularClassHomotopic
import HolomorphicAnosov.Topology.LoopSingularClassRefl

noncomputable section
open CategoryTheory
universe u
namespace HolomorphicAnosov.Topology

/-- A path chain plus its reversed-path chain is a boundary.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 proof p.166. A path followed by
its reverse is homotopic relative endpoints to the constant loop, so its class
is zero and it bounds a two-chain. Add the concatenation triangle boundary. -/
theorem pathSymm_singular_boundary {X : Type u} [TopologicalSpace X]
    {x y : X} (α : Path x y) :
    ∃ c : (integralSingularChains X).X 2,
      ((integralSingularChains X).d 2 1) c = pathSingularChain α + pathSingularChain α.symm := by
  have hz : loopSingularClass (α.trans α.symm) = 0 :=
    (loopSingularClass_homotopic (Path.Homotopic.trans_symm α)).trans (loopSingularClass_refl x)
  obtain ⟨c, hc⟩ := (loopSingularClass_eq_zero_iff _).1 hz
  obtain ⟨t, ht⟩ := pathTrans_singular_boundary α α.symm
  refine ⟨c + t, ?_⟩
  simp only [map_add, hc, ht]
  abel
end HolomorphicAnosov.Topology
