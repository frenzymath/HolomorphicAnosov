import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.LabelCardLeOverlapMultiplicity
import HolomorphicAnosov.Dynamics.Bowen.BowenBasicSetMarkovCoding

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter
open Set
open BowenBasicSetCoding
open scoped Classical
noncomputable section

/-- The size of a single-coordinate rigid coding fibre is at most the rectangle
overlap multiplicity. Evaluate codes at time zero: itinerary membership puts the
label in the rectangles containing the image, and rigidity makes evaluation
injective. This derives the q-bound from labels, independently of any larger
uniform coding multiplicity bound D. Source: Manning (1971), pp.217–219. -/
theorem coding_fibre_card_le_overlapMultiplicity {X : Type*} {N : ℕ}
    (R : Fin N → Set X) (B : Fin N → Fin N → Prop) (coding : CodeSpace B → X)
    (x : X) (horbit : ∀ a, coding a ∈ R (a.val 0))
    (hrigid : ∀ a b : CodeSpace B, coding a = x → coding b = x →
      (∃ j : ℤ, a.val j = b.val j) → a = b) :
    Nat.card {a : CodeSpace B // coding a = x} ≤ overlapMultiplicity R := by
  let label : {a : CodeSpace B // coding a = x} → {i : Fin N // x ∈ R i} :=
    fun a ↦ ⟨a.val.val 0, by simpa only [a.property] using horbit a.val⟩
  have hinj : Function.Injective label := by
    intro a b hab
    apply Subtype.ext
    exact hrigid a.val b.val a.property b.property ⟨0, congrArg Subtype.val hab⟩
  exact (Nat.card_le_card_of_injective label hinj).trans (label_card_le_overlapMultiplicity R x)

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter
