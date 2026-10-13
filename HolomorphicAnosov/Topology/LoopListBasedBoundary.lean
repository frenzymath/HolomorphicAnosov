import HolomorphicAnosov.Topology.PathSingularChain
import HolomorphicAnosov.Topology.PathTransSingularBoundary
import HolomorphicAnosov.Topology.PathConjugateSingularBoundary
import HolomorphicAnosov.Topology.ConstantPathSingularBoundary
import Mathlib.Algebra.BigOperators.Group.List.Basic

noncomputable section
open CategoryTheory
universe u
namespace HolomorphicAnosov.Topology

/-- A finite sum of loop chains in a path-connected space is homologous to
one loop at any prescribed basepoint.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 proof p.167. Transport each
loop along a connecting path, preserving its chain modulo a two-boundary,
and concatenate successively using the concatenation triangle. The empty sum
is represented by the constant loop, whose chain is a two-boundary. -/
theorem loopList_based_boundary {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    (x : X) (l : List (Σ y : X, Path y y)) :
    ∃ (α : Path x x) (c : (integralSingularChains X).X 2),
      ((integralSingularChains X).d 2 1) c =
        (l.map (fun p ↦ pathSingularChain p.2)).sum - pathSingularChain α := by
  induction l with
  | nil =>
    obtain ⟨c, hc⟩ := constantPath_singular_boundary x
    exact ⟨Path.refl x, -c, by simp [hc]⟩
  | cons p l ih =>
    obtain ⟨β, c, hc⟩ := ih
    let γ := PathConnectedSpace.somePath x p.1
    let α := (γ.trans p.2).trans γ.symm
    obtain ⟨b, hb⟩ := pathConjugate_singular_boundary γ p.2
    obtain ⟨t, ht⟩ := pathTrans_singular_boundary α β
    refine ⟨α.trans β, -b + c + t, ?_⟩
    simp only [map_add, map_neg, hb, hc, ht, List.map_cons, List.sum_cons]
    dsimp [α]
    abel
end HolomorphicAnosov.Topology
