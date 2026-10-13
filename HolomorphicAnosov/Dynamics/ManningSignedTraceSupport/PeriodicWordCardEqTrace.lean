import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.TupleMatching
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.Transition
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicWord
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.TraceEqCardCycles

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- The trace of the matching matrix counts the positive periodic tuple words of the corresponding composition. (Manning, pp. 218–219) -/
theorem periodicWord_card_eq_trace {Λ : Type u} {N r m : ℕ}
    (R : Fin N → Set Λ) (T : Matrix (Fin N) (Fin N) ℤ)
    (c : Composition r) (hm : 0 < m) :
    (Nat.card (PeriodicWord R T c hm) : ℤ) = Matrix.trace (transition R T c ^ m) := by
  exact (MatrixCounting.trace_eq_card_cycles (TupleMatching R T c) hm).symm


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
