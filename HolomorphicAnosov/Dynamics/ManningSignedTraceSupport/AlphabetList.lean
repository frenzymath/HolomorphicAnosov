import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.Alphabet

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- Manning p.217: the actual ordered list underlying an alphabet symbol. -/
def alphabetList {Λ : Type u} {N r : ℕ} {R : Fin N → Set Λ} {c : Composition r}
    (s : Alphabet R c) : List (Finset (Fin N)) := List.ofFn s.val


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
