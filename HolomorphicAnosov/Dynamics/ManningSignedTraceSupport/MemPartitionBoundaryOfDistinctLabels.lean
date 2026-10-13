import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ProperRelativeMarkovPartitionG7
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PartitionBoundary
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.DistinctRectanglesFrontier

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- A point belonging to two distinct original rectangles lies in the union of their relative frontiers. -/
theorem mem_partitionBoundary_of_distinct_labels {M : Type*} [MetricSpace M]
    {f : M ≃ₜ M} {Λ : Set M} (P : ProperRelativeMarkovPartition f Λ)
    {i j : Fin P.N} (hij : i ≠ j) {x : Λ}
    (hxi : x ∈ P.rectangles i) (hxj : x ∈ P.rectangles j) :
    x ∈ partitionBoundary P :=
  Set.mem_iUnion.mpr ⟨i, distinct_rectangles_frontier P hij hxi hxj⟩


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
