import HolomorphicAnosov.Topology.PathSingularChain
import HolomorphicAnosov.Topology.PathSingularChainInduction
import HolomorphicAnosov.Topology.PathSingularChainIntegerPositive

noncomputable section
open CategoryTheory
universe u
namespace HolomorphicAnosov.Topology

/-- Every native singular one-chain is homologous to a finite positive sum of
path chains. Source: Hatcher, Algebraic Topology, Theorem 2A.1 proof p.167.
Induct on the finite integer path expansion. The zero case has empty list;
addition concatenates lists and adds boundary witnesses; each integer multiple
is replaced by repeated copies of the original or reversed path. -/
theorem singularOneChain_positive_paths {X : Type u} [TopologicalSpace X]
    (a : (integralSingularChains X).X 1) :
    ∃ (l : List (Σ x y : X, Path x y)) (c : (integralSingularChains X).X 2),
      ((integralSingularChains X).d 2 1) c = a -
        (l.map (fun p ↦ pathSingularChain p.2.2)).sum := by
  apply pathSingularChain_induction
    (fun a ↦ ∃ (l : List (Σ x y : X, Path x y)) (c : (integralSingularChains X).X 2),
      ((integralSingularChains X).d 2 1) c = a -
        (l.map (fun p ↦ pathSingularChain p.2.2)).sum)
  · exact ⟨[], 0, by simp⟩
  · intro a b ha hb
    obtain ⟨l, c, hc⟩ := ha
    obtain ⟨k, d, hd⟩ := hb
    refine ⟨l ++ k, c + d, ?_⟩
    simp only [map_add, hc, hd, List.map_append, List.sum_append]
    abel
  · exact fun α z ↦ pathSingularChain_integer_positive α z
end HolomorphicAnosov.Topology
