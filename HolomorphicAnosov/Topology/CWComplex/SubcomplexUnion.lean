import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.CWComplex.Classical.Subcomplex

namespace HolomorphicAnosov

/-- The union of two CW subcomplexes is a subcomplex with the union of
their cell-index families. Source: Hatcher, Algebraic Topology, section 0,
subcomplexes, as used for A union the n-skeleton in Theorem 4.8 p.349.
Their carriers are closed, so their union is closed. A point belongs to
the union precisely when it belongs to an open cell selected by either
index family. This is exactly the subcomplex defining union axiom. -/
theorem cw_subcomplex_union
    {X : Type*} [TopologicalSpace X] (C : Set X) [Topology.CWComplex C]
    (A B : Topology.CWComplex.Subcomplex C) :
    ∃ D : Topology.CWComplex.Subcomplex C,
      (D : Set X) = (A : Set X) ∪ (B : Set X) ∧
      ∀ n i, i ∈ D.I n ↔ i ∈ A.I n ∨ i ∈ B.I n := by
  have hA : (⋃ (n : ℕ) (i : A.I n), Topology.CWComplex.openCell n i.val) = (A : Set X) := by
    simpa only [Set.empty_union] using A.union
  have hB : (⋃ (n : ℕ) (i : B.I n), Topology.CWComplex.openCell n i.val) = (B : Set X) := by
    simpa only [Set.empty_union] using B.union
  let D : Topology.CWComplex.Subcomplex C := {
    carrier := (A : Set X) ∪ (B : Set X)
    I := fun n ↦ A.I n ∪ B.I n
    closed' := A.closed.union B.closed
    union' := by
      rw [Set.empty_union, ← hA, ← hB]
      ext x
      simp only [Set.mem_iUnion, Subtype.exists, Set.mem_union]
      aesop }
  exact ⟨D, rfl, fun _ _ ↦ Iff.rfl⟩

end HolomorphicAnosov
