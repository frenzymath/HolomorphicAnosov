import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.NextTime
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PathEdges
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SnocTailNext

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MatrixCounting

open Set
open scoped BigOperators Classical
noncomputable section

/-- A cyclic path is the finite edge predicate used for a periodic word. -/
theorem pathEdges_cycle {A : Type*} (B : A → A → Prop) {m : ℕ}
    (w : Fin (m + 1) → A) :
    PathEdges B (w 0) (w 0) (Fin.tail w) ↔
      ∀ i, B (w i) (w (nextTime (Nat.succ_pos m) i)) := by
  unfold PathEdges
  rw [Fin.cons_self_tail]
  simp_rw [snoc_tail_next]


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MatrixCounting
