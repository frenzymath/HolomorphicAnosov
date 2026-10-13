import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- Manning p.218: one block can be bijectively matched using exactly the T-edges. -/
def BlockMatching {N : ℕ} (T : Matrix (Fin N) (Fin N) ℤ)
    (s t : Finset (Fin N)) : Prop :=
  ∃ e : ↥s ≃ ↥t, ∀ i : ↥s, T i.val (e i).val = 1


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
