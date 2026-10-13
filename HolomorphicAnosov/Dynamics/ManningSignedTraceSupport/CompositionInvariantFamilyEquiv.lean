import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.BoundedInvariantBlockFamily
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PositiveComposition

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open scoped Classical
noncomputable section

/-- Invariant families with sizes prescribed by a positive composition are
exactly the bounded-length invariant families whose ordered cardinality list
is that composition. The list equality fixes the length tag; equality at every
list position fixes the block sizes. Source: Manning (1971), pp.217–219. -/
def compositionInvariantFamilyEquiv {A : Type*} [DecidableEq A] (g : A ≃ A)
    {q : ℕ} (c : PositiveComposition q) :
    {S : Fin c.2.length → Finset A // (∀ k, (S k).Nonempty) ∧
      (∀ k, (S k).card = c.2.blocksFun k) ∧
      (Pairwise fun k j ↦ Disjoint (S k) (S j)) ∧ ∀ k, (S k).image g = S k} ≃
    {U : BoundedInvariantBlockFamily g q //
      c.2.blocks = List.ofFn (fun i ↦ (U.2.val i).card)} := by
  classical
  let k : Fin (q + 1) := ⟨c.2.length,
    lt_of_le_of_lt c.2.length_le (by omega)⟩
  have hk : 0 < k.val := c.2.length_pos_of_pos (Nat.succ_pos _)
  let f := fun S : {S : Fin c.2.length → Finset A // (∀ k, (S k).Nonempty) ∧
      (∀ k, (S k).card = c.2.blocksFun k) ∧
      (Pairwise fun k j ↦ Disjoint (S k) (S j)) ∧ ∀ k, (S k).image g = S k} ↦
    (⟨⟨k, ⟨S.val, hk, S.property.1, S.property.2.2.1, S.property.2.2.2⟩⟩, by
      change c.2.blocks = List.ofFn (fun i ↦ (S.val i).card)
      rw [show (fun i ↦ (S.val i).card) = c.2.blocksFun from funext S.property.2.1]
      exact c.2.ofFn_blocksFun.symm⟩ :
      {U : BoundedInvariantBlockFamily g q //
        c.2.blocks = List.ofFn (fun i ↦ (U.2.val i).card)})
  apply Equiv.ofBijective f
  constructor
  · intro S V h
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    have hh := eq_of_heq (Sigma.mk.inj h').2
    exact Subtype.mk.inj hh
  · rintro ⟨⟨n, ⟨S, hn, hne, hdis, hinv⟩⟩, hlist⟩
    have hnk : n = k := by
      apply Fin.ext
      have hlen := congrArg List.length hlist
      simpa only [List.length_ofFn] using hlen.symm
    subst n
    have hcard : ∀ i, (S i).card = c.2.blocksFun i := by
      have heq : List.ofFn (fun i ↦ (S i).card) = List.ofFn c.2.blocksFun := by
        rw [Composition.ofFn_blocksFun]
        exact hlist.symm
      exact congrFun (List.ofFn_inj.mp heq)
    refine ⟨⟨S, hne, hcard, hdis, hinv⟩, ?_⟩
    rfl

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
