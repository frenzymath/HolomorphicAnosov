import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.OverlapMultiplicity
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.Alphabet
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.AlphabetUnionCard

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- Every actual alphabet symbol uses at most the maximum number of rectangle
labels meeting at one point. The witness is the symbol's own common point. -/
theorem alphabet_total_le_overlapMultiplicity {Λ : Type u} {N r : ℕ}
    (R : Fin N → Set Λ) (c : Composition r) (s : Alphabet R c) :
    r ≤ overlapMultiplicity R := by
  classical
  let labels : Finset (Fin N) := Finset.univ.biUnion fun k : Fin c.length ↦ s.val k
  obtain ⟨x, hx⟩ := s.property.2.2.2
  have hcommon : ∃ x : Λ, ∀ i ∈ labels, x ∈ R i := by
    refine ⟨x, ?_⟩
    intro i hi
    obtain ⟨k, _, hik⟩ := Finset.mem_biUnion.mp hi
    exact hx k i hik
  have hsup := Finset.le_sup
    (f := fun a : Finset (Fin N) ↦ if ∃ x : Λ, ∀ i ∈ a, x ∈ R i then a.card else 0)
    (Finset.mem_univ labels)
  change (if ∃ x : Λ, ∀ i ∈ labels, x ∈ R i then labels.card else 0) ≤
    overlapMultiplicity R at hsup
  rw [ite_eq_left hcommon, alphabet_union_card R c s] at hsup
  exact hsup


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
