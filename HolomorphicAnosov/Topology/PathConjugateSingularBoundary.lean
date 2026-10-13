import HolomorphicAnosov.Topology.PathSingularChain
import HolomorphicAnosov.Topology.PathTransSingularBoundary
import HolomorphicAnosov.Topology.PathSymmSingularBoundary

noncomputable section
open CategoryTheory
universe u
namespace HolomorphicAnosov.Topology

/-- Transporting a loop along a connecting path changes its chain by a boundary.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 proof p.167, basepoint transport
in the surjectivity proof. Use the two concatenation triangles, and cancel the
connecting path with its reverse using their singular two-chain boundary. -/
theorem pathConjugate_singular_boundary {X : Type u} [TopologicalSpace X]
    {x y : X} (γ : Path x y) (α : Path y y) :
    ∃ c : (integralSingularChains X).X 2,
      ((integralSingularChains X).d 2 1) c =
        pathSingularChain ((γ.trans α).trans γ.symm) - pathSingularChain α := by
  obtain ⟨c₀, h₀⟩ := pathSymm_singular_boundary γ
  obtain ⟨c₁, h₁⟩ := pathTrans_singular_boundary γ α
  obtain ⟨c₂, h₂⟩ := pathTrans_singular_boundary (γ.trans α) γ.symm
  refine ⟨c₀ - c₁ - c₂, ?_⟩
  simp only [map_sub, h₀, h₁, h₂]
  abel
end HolomorphicAnosov.Topology
