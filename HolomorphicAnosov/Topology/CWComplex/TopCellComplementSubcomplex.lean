import Mathlib.Topology.CWComplex.Classical.Basic
import HolomorphicAnosov.Topology.CWComplex.TopCellDisjointClosedCell

namespace HolomorphicAnosov

/-- Removing a cell of maximal dimension leaves a subcomplex with precisely
that cell deleted from its indexing family. Source: Hatcher Theorem 4.8,
p.349. All other closed cells avoid the removed open cell, since their
frontiers have smaller dimension. Their open-cell union is exactly the
complement of the removed cell in the complex. The standard subcomplex
constructor therefore gives the stated carrier and indexing sets. -/
theorem cw_top_cell_complement_subcomplex
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (C : Set X) [Topology.CWComplex C]
    (k : ℕ) (i : Topology.RelCWComplex.cell C k)
    (htop : ∀ (m : ℕ), Topology.RelCWComplex.cell C m → m ≤ k) :
    ∃ W : Topology.CWComplex.Subcomplex C,
      (W : Set X) = C \ Topology.CWComplex.openCell k i ∧
      ∀ m j, j ∈ W.I m ↔ (⟨m, j⟩ : Σ n, Topology.RelCWComplex.cell C n) ≠ ⟨k, i⟩ := by
  let J (m : ℕ) : Set (Topology.RelCWComplex.cell C m) :=
    {j | (⟨m, j⟩ : Σ n, Topology.RelCWComplex.cell C n) ≠ ⟨k, i⟩}
  have hclosed : ∀ (m : ℕ) (j : J m), Topology.CWComplex.closedCell m j.val ⊆
      C \ Topology.CWComplex.openCell k i := by
    intro m j x hx
    refine ⟨Topology.CWComplex.closedCell_subset_complex m j.val hx, ?_⟩
    exact fun hi ↦ Set.disjoint_left.mp
      (cw_top_cell_disjoint_other_closed_cell k i m j.val (htop m j.val) j.property) hx hi
  have hunion : (⋃ (m : ℕ) (j : J m), Topology.CWComplex.openCell m j.val) =
      C \ Topology.CWComplex.openCell k i := by
    ext x
    constructor
    · intro hx
      obtain ⟨m, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨j, hx⟩ := Set.mem_iUnion.mp hx
      exact hclosed m j (Topology.CWComplex.openCell_subset_closedCell m j.val hx)
    · rintro ⟨hxC, hx⟩
      rw [← Topology.CWComplex.iUnion_openCell_eq_complex (C := C)] at hxC
      obtain ⟨m, hxm⟩ := Set.mem_iUnion.mp hxC
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxm
      have hj : j ∈ J m := by
        intro he
        have heq := congrArg (fun a : Σ n, Topology.RelCWComplex.cell C n ↦
          Topology.CWComplex.openCell a.1 a.2) he
        exact hx (heq ▸ hxj)
      exact Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨⟨j, hj⟩, hxj⟩⟩
  exact ⟨Topology.CWComplex.Subcomplex.mk' C _ J hclosed hunion, rfl, fun _ _ ↦ Iff.rfl⟩

end HolomorphicAnosov
