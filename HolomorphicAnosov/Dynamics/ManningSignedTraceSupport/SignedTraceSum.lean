import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PositiveComposition
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.Transition

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- Manning Section4 pp.218–219: the literal finite signed trace expression.
No equality with a fixed-point count is proved or assumed by this data definition. -/
noncomputable def signedTraceSum {Λ : Type u} {N : ℕ} (R : Fin N → Set Λ)
    (T : Matrix (Fin N) (Fin N) ℤ) (q m : ℕ) : ℤ := by
  classical
  exact ∑ c : PositiveComposition q,
    (-1) ^ (c.2.length + 1) * Matrix.trace (transition R T c.2 ^ m)


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
