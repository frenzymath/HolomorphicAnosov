import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- The maximum number of rectangle labels having a common point. (Manning, p. 217) -/
noncomputable def overlapMultiplicity {Λ : Type u} {N : ℕ} (R : Fin N → Set Λ) : ℕ := by
  classical
  exact (Finset.univ : Finset (Finset (Fin N))).sup fun s ↦
    if ∃ x : Λ, ∀ i ∈ s, x ∈ R i then s.card else 0


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
