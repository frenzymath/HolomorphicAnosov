import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

universe u v w
namespace HolomorphicAnosov.Topology

/-- Evaluating a sum of unit-coordinate finitely supported functions counts
occurrences of that coordinate in the indexing list.
Source: Hatcher, Algebraic Topology, p.167, coefficient interpretation of finite
path occurrences. Induct on the list: the empty list gives zero, and adjoining
an occurrence adds one exactly when its coordinate is the one evaluated. -/
theorem list_sum_single_count {E : Type u} {V : Type v} [DecidableEq V]
    {R : Type w} [AddCommMonoidWithOne R] (l : List E) (f : E → V) (v : V) :
    ((l.map (fun e ↦ Finsupp.single (f e) (1 : R))).sum) v =
      ((l.map f).count v : R) := by
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.map_cons, List.sum_cons, Finsupp.add_apply, ih]
    by_cases h : f e = v
    · simp [h, Nat.cast_add, add_comm]
    · simp [h, Ne.symm h]
end HolomorphicAnosov.Topology
