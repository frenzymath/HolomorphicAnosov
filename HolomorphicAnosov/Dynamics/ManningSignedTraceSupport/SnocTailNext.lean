import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.NextTime

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MatrixCounting

open Set
open scoped BigOperators Classical
noncomputable section

/-- Removing the first vertex and appending it at the end is cyclic successor. -/
theorem snoc_tail_next {A : Type*} {m : ℕ} (w : Fin (m + 1) → A)
    (i : Fin (m + 1)) :
    Fin.snoc (α := fun _ ↦ A) (Fin.tail w) (w 0) i =
      w (nextTime (Nat.succ_pos m) i) := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · rw [Fin.snoc_last]
    congr 1
    apply Fin.ext
    simp [nextTime]
  · rw [Fin.snoc_castSucc]
    change w j.succ = w (nextTime (Nat.succ_pos m) j.castSucc)
    congr 1
    apply Fin.ext
    dsimp [nextTime]
    rw [Nat.mod_eq_of_lt (Nat.succ_lt_succ j.isLt)]


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MatrixCounting
