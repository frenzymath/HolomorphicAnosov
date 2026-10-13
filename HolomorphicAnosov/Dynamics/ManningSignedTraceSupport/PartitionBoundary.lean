import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ProperRelativeMarkovPartitionG7

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- The union of the relative frontiers of all rectangles in the partition. (Manning, pp. 216–217) -/
def partitionBoundary {M : Type*} [MetricSpace M]
    {f : M ≃ₜ M} {Λ : Set M} (P : ProperRelativeMarkovPartition f Λ) : Set Λ :=
  ⋃ i, frontier (P.rectangles i)


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
