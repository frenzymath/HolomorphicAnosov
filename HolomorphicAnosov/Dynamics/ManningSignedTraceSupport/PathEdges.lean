import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MatrixCounting

open Set
open scoped BigOperators Classical
noncomputable section

/-- The predicate describing a path of length `m+1` with fixed endpoints and `m` intermediate vertices. (Manning, pp. 218–219) -/
def PathEdges {A : Type*} (B : A → A → Prop) {m : ℕ}
    (a b : A) (w : Fin m → A) : Prop :=
  ∀ i : Fin (m + 1), B (Fin.cons (α := fun _ ↦ A) a w i) (Fin.snoc (α := fun _ ↦ A) w b i)


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MatrixCounting
