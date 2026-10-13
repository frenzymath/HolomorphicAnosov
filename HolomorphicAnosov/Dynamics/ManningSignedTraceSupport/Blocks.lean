import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- Manning p.217: an ordered family of finite rectangle-label blocks. -/
abbrev Blocks (N : ℕ) {r : ℕ} (c : Composition r) :=
  Fin c.length → Finset (Fin N)


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
