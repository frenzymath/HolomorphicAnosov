import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.Alphabet
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.TupleMatching
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.NextTime

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- A periodic tuple word of period `m`, allowing smaller least period. (Manning, pp. 218–219) -/
abbrev PeriodicWord {Λ : Type u} {N r m : ℕ} (R : Fin N → Set Λ)
    (T : Matrix (Fin N) (Fin N) ℤ) (c : Composition r) (hm : 0 < m) :=
  {w : Fin m → Alphabet R c // ∀ t, TupleMatching R T c (w t) (w (nextTime hm t))}

noncomputable instance {Λ : Type u} {N r m : ℕ} (R : Fin N → Set Λ)
    (T : Matrix (Fin N) (Fin N) ℤ) (c : Composition r) (hm : 0 < m) :
    Fintype (PeriodicWord R T c hm) := Fintype.ofFinite _


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
