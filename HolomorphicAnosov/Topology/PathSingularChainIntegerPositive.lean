import HolomorphicAnosov.Topology.PathSingularChain
import HolomorphicAnosov.Topology.PathSymmSingularBoundary
import Mathlib.Algebra.BigOperators.Group.List.Basic

noncomputable section
open CategoryTheory
universe u
namespace HolomorphicAnosov.Topology

/-- Every integer multiple of a path chain is homologous to a finite positive
list of path chains, allowing path reversal.
Source: Hatcher, Algebraic Topology, pp.166–167, identity (iv) and the first
surjectivity reduction. A nonnegative coefficient gives repeated copies.
For a negative coefficient repeat the reversed path and subtract the same
number of copies of the path-plus-reversal two-chain. -/
theorem pathSingularChain_integer_positive {X : Type u} [TopologicalSpace X]
    {x y : X} (α : Path x y) (z : ℤ) :
    ∃ (l : List (Σ x y : X, Path x y)) (c : (integralSingularChains X).X 2),
      ((integralSingularChains X).d 2 1) c = z • pathSingularChain α -
        (l.map (fun p ↦ pathSingularChain p.2.2)).sum := by
  cases z with
  | ofNat n =>
    refine ⟨List.replicate n ⟨x, y, α⟩, 0, ?_⟩
    simp
  | negSucc n =>
    obtain ⟨b, hb⟩ := pathSymm_singular_boundary α
    refine ⟨List.replicate (n + 1) ⟨y, x, α.symm⟩, -((n + 1) • b), ?_⟩
    simp only [map_neg, map_nsmul, hb, List.map_replicate, List.sum_replicate]
    rw [Int.negSucc_eq, neg_zsmul, ← Nat.cast_add_one, natCast_zsmul]
    simp only [nsmul_add]
    abel
end HolomorphicAnosov.Topology
