import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ProperRelativeMarkovPartitionG7
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.Alphabet
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.TupleMatching
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.Transition
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.OneComposition
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SymbolLabel
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SymbolLabelBlock
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.OriginalTransition
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.BlockMatchingSingleton

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- Under the singleton-label bijection, the matching matrix for the one-block composition equals the original transition matrix. (Manning, p. 218) -/
theorem oneComposition_transition {M : Type*} [MetricSpace M]
    {f : M ≃ₜ M} {Λ : Set M} (P : ProperRelativeMarkovPartition f Λ)
    (s t : Alphabet P.rectangles oneComposition) :
    transition P.rectangles (originalTransition P) oneComposition s t =
      originalTransition P (symbolLabel P.rectangles s) (symbolLabel P.rectangles t) := by
  classical
  have hm : TupleMatching P.rectangles (originalTransition P) oneComposition s t ↔
      originalTransition P (symbolLabel P.rectangles s) (symbolLabel P.rectangles t) = 1 := by
    constructor
    · intro h
      let z : Fin oneComposition.length := ⟨0, by decide⟩
      have h0 := h z
      rw [symbolLabel_block P.rectangles s z, symbolLabel_block P.rectangles t z,
        blockMatching_singleton] at h0
      exact h0
    · intro h k
      rw [symbolLabel_block, symbolLabel_block, blockMatching_singleton]
      exact h
  rw [transition, hm]
  unfold originalTransition
  split_ifs <;> norm_num at *


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
