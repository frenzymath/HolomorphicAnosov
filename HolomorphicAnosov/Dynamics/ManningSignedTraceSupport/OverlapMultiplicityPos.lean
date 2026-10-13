import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.OverlapMultiplicity

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- For a nonempty covered set, the overlap multiplicity is positive. (Manning, p. 217) -/
theorem overlapMultiplicity_pos {Λ : Type u} {N : ℕ} (R : Fin N → Set Λ)
    (hne : Nonempty Λ) (hcover : ∀ x : Λ, ∃ i, x ∈ R i) :
    1 ≤ overlapMultiplicity R := by
  classical
  obtain ⟨x⟩ := hne
  obtain ⟨i, hi⟩ := hcover x
  have hcommon : ∃ y : Λ, ∀ j ∈ ({i} : Finset (Fin N)), y ∈ R j :=
    ⟨x, fun j hj ↦ (Finset.mem_singleton.mp hj) ▸ hi⟩
  unfold overlapMultiplicity
  have h := Finset.le_sup
    (f := fun s : Finset (Fin N) ↦ if ∃ y : Λ, ∀ j ∈ s, y ∈ R j then s.card else 0)
    (Finset.mem_univ ({i} : Finset (Fin N)))
  simpa only [ite_eq_left hcommon, Finset.card_singleton] using h


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
