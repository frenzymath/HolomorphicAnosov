import HolomorphicAnosov.Topology.GallierXuSurfacePresentation

noncomputable section
open Set Topology _root_.Topology
namespace HolomorphicAnosov.Topology.GallierXu

/-- Consecutive entries of a finite list are related by its path-edge relation. -/
lemma pathEdge_succ {N : ℕ} (l : List (Fin N)) (i : ℕ)
    (hi : i + 1 < l.length) :
    pathEdge l (l.get ⟨i + 1, hi⟩) (l.get ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩) := by
  exact ⟨i, hi, Or.inr ⟨rfl, rfl⟩⟩

/-- Every entry of a nonempty finite interval link is connected to its first entry by
`EqvGen pathEdge`.  This is the list-level fan chain used at interval-link vertices. -/
lemma pathEdge_chain_to_first {N : ℕ} (l : List (Fin N)) (h0 : 0 < l.length) :
    ∀ (n : ℕ) (hn : n < l.length),
      Relation.EqvGen (pathEdge l) (l.get ⟨n, hn⟩) (l.get ⟨0, h0⟩) := by
  intro n
  induction n with
  | zero =>
      intro hn
      exact Relation.EqvGen.refl _
  | succ n ih =>
      intro hn
      have hn' : n < l.length := Nat.lt_trans (Nat.lt_succ_self n) hn
      exact Relation.EqvGen.trans _ _ _
        (Relation.EqvGen.rel _ _ (pathEdge_succ l n hn))
        (ih hn')

end HolomorphicAnosov.Topology.GallierXu
