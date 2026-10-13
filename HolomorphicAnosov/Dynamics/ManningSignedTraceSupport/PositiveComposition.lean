import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- A positive composition is an ordered list of positive parts with total size at most `q`. (Manning, p. 217) -/
abbrev PositiveComposition (q : ℕ) := Σ r : Fin q, Composition (r.val + 1)


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
