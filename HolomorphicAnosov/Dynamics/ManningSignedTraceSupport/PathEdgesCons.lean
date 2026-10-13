import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PathEdges

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MatrixCounting

open Set
open scoped BigOperators Classical
noncomputable section

/-- Removing the first edge of a path leaves the corresponding tail path. -/
theorem pathEdges_cons {A : Type*} (B : A → A → Prop) {m : ℕ}
    (a b c : A) (w : Fin m → A) :
    PathEdges B a b (Fin.cons c w) ↔ B a c ∧ PathEdges B c b w := by
  unfold PathEdges
  rw [← Fin.cons_snoc_eq_snoc_cons]
  simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MatrixCounting
