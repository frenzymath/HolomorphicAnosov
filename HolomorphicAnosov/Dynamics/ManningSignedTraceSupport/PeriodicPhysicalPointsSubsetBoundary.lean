import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ProperRelativeMarkovPartitionG7
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicWord
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicPhysicalPoints
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.OriginalTransition
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PartitionBoundary
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.MemPartitionBoundaryOfDistinctLabels
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.AlphabetHasDistinctLabels

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- If a positive periodic word has distinct labels, every related physical point lies in the partition boundary. (Manning, pp. 218–219) -/
theorem periodicPhysicalPoints_subset_boundary {M : Type*} [MetricSpace M]
    {f : M ≃ₜ M} {Λ : Set M} (P : ProperRelativeMarkovPartition f Λ)
    {r m : ℕ} (c : Composition (r + 1)) (hc : c.blocks ≠ [1]) (hm : 0 < m)
    (w : PeriodicWord P.rectangles (originalTransition P) c hm) :
    periodicPhysicalPoints P.rectangles (originalTransition P) c P.onSet hm w ⊆
      partitionBoundary P := by
  intro x hx
  let t : Fin m := ⟨0, hm⟩
  obtain ⟨k, l, i, j, hi, hj, hij⟩ :=
    alphabet_has_distinct_labels P.rectangles c hc (w.val t)
  apply mem_partitionBoundary_of_distinct_labels P hij
  · simpa [t] using hx.2 t k i hi
  · simpa [t] using hx.2 t l j hj


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
