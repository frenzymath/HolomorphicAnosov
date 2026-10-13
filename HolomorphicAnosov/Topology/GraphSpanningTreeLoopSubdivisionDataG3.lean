import HolomorphicAnosov.Topology.OpenCoverPathSubdivision

namespace HolomorphicAnosov

/-- The compact-loop finite subdivision interface used by the spanning-tree quotient proof.

Source: Hatcher, *Algebraic Topology*, Lemma 1.15, p.35.  This is the exact
finite data needed by the graph quotient argument: each continuous path has a
finite monotone subdivision whose closed subpaths lie in selected members of an
open cover.  The proof delegates only to the pinned interval subdivision theorem;
no graph, finiteness, or local-finiteness hypothesis is introduced.
-/
theorem graph_spanning_tree_loop_subdivision_data_g3
    {X : Type*} [TopologicalSpace X] {x y : X} {ι : Type*}
    (γ : Path x y) (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ t : unitInterval, ∃ i, γ t ∈ U i) :
    ∃ n : ℕ, 0 < n ∧ ∃ t : Fin (n + 1) → unitInterval,
      t 0 = 0 ∧ t (Fin.last n) = 1 ∧ Monotone t ∧
        ∃ assigned : Fin n → ι, ∀ j : Fin n,
          Set.range (γ.subpath (t j.castSucc) (t j.succ)) ⊆ U (assigned j) := by
  exact exists_openCover_pathSubdivision γ U hU hcover

end HolomorphicAnosov
