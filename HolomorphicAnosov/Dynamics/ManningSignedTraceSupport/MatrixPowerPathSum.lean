import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PathEdges
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PathEdgesCons
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.EdgeMatrix

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MatrixCounting

open Set
open scoped BigOperators Classical
noncomputable section

/-- Matrix powers count finite directed paths with prescribed endpoints, including paths of nonminimal period. (Manning, pp. 218–219) -/
theorem matrix_power_path_sum {A : Type*} [Fintype A] [DecidableEq A]
    (B : A → A → Prop) (m : ℕ) (a b : A) :
    (edgeMatrix B ^ (m + 1)) a b =
      ∑ w : Fin m → A, if PathEdges B a b w then (1 : ℤ) else 0 := by
  classical
  induction m generalizing a b with
  | zero => simp [PathEdges, edgeMatrix, Fin.forall_fin_one, Fin.snoc]
  | succ m ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [ih]
    simp only [edgeMatrix]
    simp_rw [Finset.mul_sum]
    rw [← Fintype.sum_prod_type (fun p : A × (Fin m → A) ↦
      (if B a p.1 then (1 : ℤ) else 0) * (if PathEdges B p.1 b p.2 then 1 else 0))]
    symm
    apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 1) ↦ A)).symm
    intro w
    change (if PathEdges B a b w then (1 : ℤ) else 0) =
      (if B a (w 0) then 1 else 0) *
        (if PathEdges B (w 0) b (Fin.tail w) then (1 : ℤ) else 0)
    have hw : w = Fin.cons (w 0) (Fin.tail w) := (Fin.cons_self_tail w).symm
    have hpath : PathEdges B a b w ↔ B a (w 0) ∧ PathEdges B (w 0) b (Fin.tail w) := by
      conv_lhs => rw [hw]
      exact pathEdges_cons B a b (w 0) (Fin.tail w)
    rw [hpath]
    split_ifs <;> simp_all


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MatrixCounting
