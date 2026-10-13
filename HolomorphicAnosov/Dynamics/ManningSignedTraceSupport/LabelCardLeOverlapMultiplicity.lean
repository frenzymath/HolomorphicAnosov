import Mathlib.SetTheory.Cardinal.Finite
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.OverlapMultiplicity

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open Set
open scoped Classical
noncomputable section

/-- The labels of rectangles containing one point form a common-intersection
family and hence have cardinal at most Manning's overlap multiplicity q.
This includes points outside the cover, whose label set is empty. -/
theorem label_card_le_overlapMultiplicity {X : Type*} {N : ℕ}
    (R : Fin N → Set X) (x : X) :
    Nat.card {i : Fin N // x ∈ R i} ≤ overlapMultiplicity R := by
  classical
  let s := Finset.univ.filter fun i ↦ x ∈ R i
  have hs : ∃ y : X, ∀ i ∈ s, y ∈ R i := by
    exact ⟨x, fun i hi ↦ (Finset.mem_filter.mp hi).2⟩
  have hsup := Finset.le_sup
    (f := fun a : Finset (Fin N) ↦ if ∃ y : X, ∀ i ∈ a, y ∈ R i then a.card else 0)
    (Finset.mem_univ s)
  change (if ∃ y : X, ∀ i ∈ s, y ∈ R i then s.card else 0) ≤ overlapMultiplicity R at hsup
  rw [ite_eq_left hs] at hsup
  simpa [s, Nat.card_eq_fintype_card, Fintype.card_subtype] using hsup

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
