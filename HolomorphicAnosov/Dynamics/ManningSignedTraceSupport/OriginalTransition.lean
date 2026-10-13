import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ProperRelativeMarkovPartitionG7

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- The zero-one transition matrix of a proper relative Markov partition, with an entry recording whether the corresponding relative interiors meet after applying the map. (Manning, p. 216) -/
noncomputable def originalTransition {M : Type*} [MetricSpace M]
    {f : M ≃ₜ M} {Λ : Set M} (P : ProperRelativeMarkovPartition f Λ) :
    Matrix (Fin P.N) (Fin P.N) ℤ :=
  fun i j ↦ if (P.onSet '' interior (P.rectangles i) ∩
    interior (P.rectangles j)).Nonempty then 1 else 0


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
