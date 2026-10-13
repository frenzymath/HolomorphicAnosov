import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.BlockAssignmentMem
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.Alphabet
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.LabelCardLeOverlapMultiplicity
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open Set
open scoped Classical
noncomputable section

/-- Symbols whose every label contains x are bounded by assignments of those
labels to the ordered blocks or to unused. Disjointness makes the assignment
encoding injective. The exponent is the actual number of labels at x, not the
size of the whole partition. Source: Manning (1971), pp.218–219. -/
theorem supportedAlphabet_card_bound {X : Type*} {N r : ℕ}
    (R : Fin N → Set X) (c : Composition r) (x : X) :
    Nat.card {s : Alphabet R c // ∀ k i, i ∈ s.val k → x ∈ R i} ≤
      (c.length + 1) ^ Nat.card {i : Fin N // x ∈ R i} := by
  classical
  let enc : {s : Alphabet R c // ∀ k i, i ∈ s.val k → x ∈ R i} →
      ({i : Fin N // x ∈ R i} → Option (Fin c.length)) :=
    fun s i ↦ blockAssignment s.val.val i.val
  have hinj : Function.Injective enc := by
    intro s t heq
    apply Subtype.ext
    apply Subtype.ext
    funext k
    apply Finset.ext
    intro i
    by_cases hi : x ∈ R i
    · have h := congrFun heq ⟨i, hi⟩
      change blockAssignment s.val.val i = blockAssignment t.val.val i at h
      rw [← blockAssignment_mem s.val.val s.val.property.2.2.1 i k,
        ← blockAssignment_mem t.val.val t.val.property.2.2.1 i k, h]
    · exact iff_of_false (fun hs ↦ hi (s.property k i hs))
        (fun ht ↦ hi (t.property k i ht))
  have h := Nat.card_le_card_of_injective enc hinj
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_option,
    Fintype.card_fin] using h

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
