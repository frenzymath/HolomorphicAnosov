import HolomorphicAnosov.Topology.PathSingularChain
import HolomorphicAnosov.Topology.ListEndpointBalanceSuccessor
import HolomorphicAnosov.Topology.PathTransSingularBoundary
import Mathlib.Algebra.BigOperators.Group.List.Basic

noncomputable section
open CategoryTheory
universe u
namespace HolomorphicAnosov.Topology

/-- A finite positive path list with balanced endpoint counts is homologous to
a finite list of loops, whose basepoints may differ.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 proof p.167. Induct on the
number of occurrences. Remove a loop if the first path is closed. Otherwise
balance gives another path starting at its endpoint. Replace these two paths
by their concatenation, preserving balance and the chain modulo its triangle
boundary while reducing the number of occurrences. -/
theorem pathList_balanced_loops {X : Type u} [TopologicalSpace X] [DecidableEq X]
    (l : List (Σ x y : X, Path x y))
    (hb : ∀ v, (l.map (fun p ↦ p.1)).count v = (l.map (fun p ↦ p.2.1)).count v) :
    ∃ (k : List (Σ x : X, Path x x)) (c : (integralSingularChains X).X 2),
      ((integralSingularChains X).d 2 1) c =
        (l.map (fun p ↦ pathSingularChain p.2.2)).sum -
          (k.map (fun p ↦ pathSingularChain p.2)).sum := by
  classical
  generalize hn : l.length = n
  induction n using Nat.strong_induction_on generalizing l with
  | h n ih =>
    cases l with
    | nil => exact ⟨[], 0, by simp⟩
    | cons p l =>
      rcases p with ⟨x, y, α⟩
      by_cases hxy : x = y
      · subst y
        have hbl : ∀ v, (l.map (fun p ↦ p.1)).count v =
            (l.map (fun p ↦ p.2.1)).count v := by
          intro v
          have h := hb v
          simp only [List.map_cons, List.count_cons] at h
          omega
        obtain ⟨k, c, hc⟩ := ih l.length (by simpa using hn.symm ▸ Nat.lt_succ_self l.length)
          l hbl rfl
        refine ⟨⟨x, α⟩ :: k, c, ?_⟩
        simp only [List.map_cons, List.sum_cons]
        rw [hc]
        abel
      · obtain ⟨⟨z, w, β⟩, hm, hz⟩ :=
          list_endpoint_balance_successor (fun p ↦ p.1) (fun p ↦ p.2.1) ⟨x, y, α⟩ l hxy hb
        dsimp at hz
        subst z
        obtain ⟨s, t, rfl⟩ := List.mem_iff_append.mp hm
        let q : Σ x y : X, Path x y := ⟨x, w, α.trans β⟩
        have hbn : ∀ v, ((q :: s ++ t).map (fun p ↦ p.1)).count v =
            ((q :: s ++ t).map (fun p ↦ p.2.1)).count v := by
          intro v
          have h := hb v
          simp only [List.map_cons, List.map_append, List.count_cons, List.count_append] at h ⊢
          dsimp [q]
          omega
        have hlen : (q :: s ++ t).length < n := by
          simp only [List.length_cons, List.length_append] at hn ⊢
          omega
        obtain ⟨k, c, hc⟩ := ih (q :: s ++ t).length hlen (q :: s ++ t) hbn rfl
        obtain ⟨b, hb'⟩ := pathTrans_singular_boundary α β
        refine ⟨k, b + c, ?_⟩
        simp only [map_add, hb', hc, List.map_cons, List.map_append, List.sum_cons,
          List.sum_append]
        dsimp [q]
        abel
end HolomorphicAnosov.Topology
