import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.NextTime
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PathEdges
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.EdgeMatrix
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.MatrixPowerPathSum
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PathEdgesCycle

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MatrixCounting

open Set
open scoped BigOperators Classical
noncomputable section

/-- The trace of a zero-one directed matrix counts positive cyclic words, with
all smaller least periods included. The proof expands matrix multiplication and
reindexes by the first vertex and the remaining finite tuple. Manning pp.218–219. -/
theorem trace_eq_card_cycles {A : Type*} [Fintype A] [DecidableEq A]
    (B : A → A → Prop) {m : ℕ} (hm : 0 < m) :
    Matrix.trace (edgeMatrix B ^ m) =
      (Nat.card {w : Fin m → A // ∀ i, B (w i) (w (nextTime hm i))} : ℤ) := by
  classical
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have hsum : Matrix.trace (edgeMatrix B ^ (n + 1)) =
      ∑ w : Fin (n + 1) → A,
        if ∀ i, B (w i) (w (nextTime hm i)) then (1 : ℤ) else 0 := by
    unfold Matrix.trace Matrix.diag
    simp_rw [matrix_power_path_sum]
    rw [← Fintype.sum_prod_type (fun p : A × (Fin n → A) ↦
      if PathEdges B p.1 p.1 p.2 then (1 : ℤ) else 0)]
    apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) ↦ A))
    intro p
    have h := pathEdges_cycle B (Fin.cons p.1 p.2)
    simp only [Fin.cons_zero, Fin.tail_cons] at h
    change (if PathEdges B p.1 p.1 p.2 then (1 : ℤ) else 0) =
      (if ∀ i, B (Fin.cons (α := fun _ ↦ A) p.1 p.2 i) (Fin.cons (α := fun _ ↦ A) p.1 p.2 (nextTime hm i)) then 1 else 0)
    have hm' : hm = Nat.succ_pos n := Subsingleton.elim _ _
    subst hm
    rw [h]
    split_ifs <;> rfl
  rw [hsum, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MatrixCounting
