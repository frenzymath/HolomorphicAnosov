import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PositiveComposition

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- Manning p.217: the actual nonempty ordered list of block sizes. -/
def compositionList {q : ℕ} (c : PositiveComposition q) : List ℕ := c.2.blocks


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
