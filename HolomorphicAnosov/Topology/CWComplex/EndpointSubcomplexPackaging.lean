import Mathlib.Topology.CWComplex.Classical.Subcomplex

open Set _root_.Topology
namespace HolomorphicAnosov.Topology

/-- A selected family of original cells whose closed cells lie in a carrier packages
as an actual CW subcomplex. The selected indexing family is retained as ranges.

Source: Mathlib `Topology.CWComplex.Subcomplex.mk'`, used for the endpoint
subcomplex step of Fritsch–Piccinini, *Cellular Structures in Topology*,
Theorem 2.2.2, p.58. This range-indexed formulation is an implementation lemma.
Proof: rewrite the subtype-indexed union over `range (endpoint n)` as the
supplied union, by choosing a range witness in one direction and inserting
`endpoint n i` with its range witness in the other. Apply `Subcomplex.mk'`.
Its carrier and selected index sets are definitionally the asserted ones.
No injectivity, finite indexing, or ambient openness of cells is assumed. -/
theorem endpoint_range_subcomplex
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CWComplex (univ : Set Y)]
    (β : ℕ → Type*) (endpoint : ∀ n, β n → RelCWComplex.cell (univ : Set Y) n)
    (E : Set Y)
    (hclosed : ∀ n (i : β n),
      CWComplex.closedCell (C := (univ : Set Y)) n (endpoint n i) ⊆ E)
    (hopen : (⋃ n, ⋃ i : β n,
      CWComplex.openCell (C := (univ : Set Y)) n (endpoint n i)) = E) :
    ∃ A : CWComplex.Subcomplex (univ : Set Y),
      (A : Set Y) = E ∧ ∀ n, A.I n = range (endpoint n) := by
  let I : ∀ n, Set (RelCWComplex.cell (univ : Set Y) n) := fun n => range (endpoint n)
  have hopen' : (⋃ n, ⋃ j : I n,
      CWComplex.openCell (C := (univ : Set Y)) n j) = E := by
    apply subset_antisymm
    · intro y hy
      simp only [mem_iUnion] at hy
      rcases hy with ⟨n, j, hy⟩
      rcases j.property with ⟨i, hi⟩
      rw [← hopen]
      exact mem_iUnion_of_mem n (mem_iUnion_of_mem i (hi ▸ hy))
    · intro y hy
      rw [← hopen] at hy
      rcases mem_iUnion.mp hy with ⟨n, hy⟩
      rcases mem_iUnion.mp hy with ⟨i, hi⟩
      exact mem_iUnion_of_mem n (mem_iUnion_of_mem (⟨endpoint n i, ⟨i, rfl⟩⟩ : I n) hi)
  let A : CWComplex.Subcomplex (univ : Set Y) :=
    CWComplex.Subcomplex.mk' (univ : Set Y) E I (by
      intro n j
      rcases j with ⟨j, ⟨i, rfl⟩⟩
      exact hclosed n i) hopen'
  refine ⟨A, ?_, ?_⟩
  · rfl
  · intro n
    rfl

end HolomorphicAnosov.Topology

