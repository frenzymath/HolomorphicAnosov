import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- The composition consisting of the single block of size one. (Manning, p. 218) -/
abbrev oneComposition : Composition 1 := Composition.single 1 (by decide)


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
