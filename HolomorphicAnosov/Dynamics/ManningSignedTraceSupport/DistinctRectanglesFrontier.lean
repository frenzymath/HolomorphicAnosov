import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ProperRelativeMarkovPartitionG7

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- Distinct proper partition rectangles meet only in their frontiers.
Manning pp.216,219: if a common point were interior to the first rectangle,
regular closure of the second would produce intersecting interiors. This uses
only the actual relative topology; it is valid on finite or zero-dimensional sets. -/
theorem distinct_rectangles_frontier {M : Type*} [MetricSpace M]
    {f : M ≃ₜ M} {Λ : Set M} (P : ProperRelativeMarkovPartition f Λ)
    {i j : Fin P.N} (hij : i ≠ j) {x : Λ}
    (hxi : x ∈ P.rectangles i) (hxj : x ∈ P.rectangles j) :
    x ∈ frontier (P.rectangles i) := by
  have hnot : x ∉ interior (P.rectangles i) := by
    intro hxin
    have hxcl : x ∈ closure (interior (P.rectangles j)) := by
      simpa only [P.rectangles_regularClosed j] using hxj
    obtain ⟨y, hyi, hyj⟩ :=
      (mem_closure_iff.mp hxcl) (interior (P.rectangles i)) isOpen_interior hxin
    exact (Set.disjoint_left.mp (P.disjoint_interiors i j hij)) hyi hyj
  exact ⟨subset_closure hxi, hnot⟩


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
