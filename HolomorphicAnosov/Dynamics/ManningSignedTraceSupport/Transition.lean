import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.Alphabet
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.TupleMatching

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- Manning p.218: the actual zero-one adjacency matrix, not a supplied trace operand. -/
noncomputable def transition {Λ : Type u} {N r : ℕ} (R : Fin N → Set Λ)
    (T : Matrix (Fin N) (Fin N) ℤ) (c : Composition r) :
    Matrix (Alphabet R c) (Alphabet R c) ℤ := by
  classical
  exact fun s t ↦ if TupleMatching R T c s t then 1 else 0


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
