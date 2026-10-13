import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.SetTheory.Cardinal.Finite

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open scoped BigOperators Classical
noncomputable section

/-- Reindex a weighted count of finite families by a unique finite index.
The projection from the dependent sum of index fibres is bijective by unique
existence; compatible weights therefore give equal finite sums. This abstracts
the composition reindexing in Manning (1971), pp.217–219. -/
theorem weighted_unique_index_card_sum {C A : Type*} [Fintype C] [Fintype A]
    (p : C → A → Prop) (hp : ∀ a, ∃! c, p c a) (s : C → ℤ) (w : A → ℤ)
    (hw : ∀ c a, p c a → s c = w a) :
    ∑ c : C, s c * Nat.card {a : A // p c a} = ∑ a : A, w a := by
  classical
  let f : (Σ c : C, {a : A // p c a}) → A := fun z ↦ z.2.val
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨c, a⟩ ⟨d, b⟩ hab
      change a.val = b.val at hab
      have hcd : c = d := (hp a.val).unique a.property (hab.symm ▸ b.property)
      subst d
      have ha : a = b := Subtype.ext hab
      subst b
      rfl
    · intro a
      obtain ⟨c, hc, _⟩ := hp a
      exact ⟨⟨c, ⟨a, hc⟩⟩, rfl⟩
  calc
    ∑ c : C, s c * Nat.card {a : A // p c a} =
        ∑ z : Σ c : C, {a : A // p c a}, s z.1 := by
      rw [Fintype.sum_sigma]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Nat.card_eq_fintype_card, mul_comm]
    _ = ∑ a : A, w a := Fintype.sum_bijective f hf _ _
      (fun z ↦ hw z.1 z.2.val z.2.property)

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
