import HolomorphicAnosov.Dynamics.Bowen.BowenBasicSetMarkovCoding

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter
open Set BowenBasicSetCoding
noncomputable section

/-- Coordinate evaluation identifies a rigid coding fibre with all rectangle
labels at that coordinate. The itinerary gives membership, single-coordinate
rigidity gives injectivity, and the every-label property gives surjectivity.
This is Manning's finite-fibre label identification (1971), pp.217–219, using
Bowen Proposition 12, p.914, only through explicit rigid-fibre hypotheses. -/
def fibreCoordinateEquiv {X : Type*} {N : ℕ} (B : Fin N → Fin N → Prop)
    (coding : CodeSpace B → X) (x : X) (j : ℤ) (L : Set (Fin N))
    (hmem : ∀ a, coding a = x → a.val j ∈ L)
    (hrigid : ∀ a b : CodeSpace B, coding a = x → coding b = x →
      a.val j = b.val j → a = b)
    (hlabel : ∀ i ∈ L, ∃ a : CodeSpace B, coding a = x ∧ a.val j = i) :
    {a : CodeSpace B // coding a = x} ≃ L :=
  Equiv.ofBijective (fun a ↦ ⟨a.val.val j, hmem a.val a.property⟩) ⟨by
    intro a b h
    apply Subtype.ext
    exact hrigid a.val b.val a.property b.property (congrArg Subtype.val h), by
    intro i
    obtain ⟨a, ha, hai⟩ := hlabel i.val i.property
    exact ⟨⟨a, ha⟩, Subtype.ext hai⟩⟩

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter
