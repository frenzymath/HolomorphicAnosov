import HolomorphicAnosov.Topology.GallierXuIntervalLinkChain

noncomputable section
namespace HolomorphicAnosov.Topology.GallierXu

/-- A finite interval-link path transports a generated relation between any two
chosen face representatives whenever each consecutive path edge is supplied
with a literal generator. This is the list-level vertex fan step in Lee
Proposition 6.14, p.173; the geometric lookup of the representatives is kept
as an explicit bridge hypothesis. -/
lemma eqvGen_of_interval_fan_transport {N : ℕ} {α : Type*}
    {l : List (Fin N)} (h0 : 0 < l.length)
    (R : α → α → Prop) (rep : Fin N → α)
    (hbridge : ∀ {a b : Fin N}, pathEdge l a b →
      Relation.EqvGen R (rep a) (rep b)) :
    ∀ {a b : Fin N}, a ∈ l → b ∈ l →
      Relation.EqvGen R (rep a) (rep b) := by
  intro a b ha hb
  obtain ⟨ia, rfl⟩ := List.mem_iff_get.mp ha
  obtain ⟨ib, rfl⟩ := List.mem_iff_get.mp hb
  have transport : ∀ n : ℕ, ∀ hn : n < l.length,
      Relation.EqvGen R (rep (l.get ⟨n, hn⟩)) (rep (l.get ⟨0, h0⟩)) := by
    intro n
    induction n with
    | zero => intro hn; exact Relation.EqvGen.refl _
    | succ n ih =>
      intro hn
      have hn' : n < l.length := Nat.lt_trans (Nat.lt_succ_self n) hn
      exact Relation.EqvGen.trans _ _ _
        (hbridge (pathEdge_succ l n hn)) (ih hn')
  have hiaR := transport ia.val ia.isLt
  have hibR := transport ib.val ib.isLt
  exact Relation.EqvGen.trans _ _ _ hiaR hibR.symm

end HolomorphicAnosov.Topology.GallierXu
