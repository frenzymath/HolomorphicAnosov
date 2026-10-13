import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- The successor operation on positions in a positive-length cyclic word. (Manning, §4, p. 218) -/
def nextTime {m : ℕ} (hm : 0 < m) (t : Fin m) : Fin m :=
  ⟨(t.val + 1) % m, Nat.mod_lt _ hm⟩


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
