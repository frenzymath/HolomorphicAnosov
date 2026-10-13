import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PositiveComposition

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- Manning p.217: the finite collection of ordered positive compositions. -/
def compositions (q : ℕ) : Finset (PositiveComposition q) := Finset.univ


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
