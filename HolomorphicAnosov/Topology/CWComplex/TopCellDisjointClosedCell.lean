import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.CWComplex.Classical.Subcomplex

namespace HolomorphicAnosov

/-- A top-dimensional open cell is disjoint from every other closed cell.
Source: Hatcher Theorem 4.8, p.349, removing a highest-dimensional cell.
Distinct open cells are disjoint. The frontier of any cell of dimension
at most k is a union of cells of dimension strictly below k, so it is
also disjoint from the chosen open k-cell. -/
theorem cw_top_cell_disjoint_other_closed_cell
    {X : Type*} [TopologicalSpace X] {C : Set X} [Topology.CWComplex C]
    (k : ℕ) (i : Topology.RelCWComplex.cell C k)
    (m : ℕ) (j : Topology.RelCWComplex.cell C m) (hm : m ≤ k)
    (hne : (⟨m, j⟩ : Σ n, Topology.RelCWComplex.cell C n) ≠ ⟨k, i⟩) :
    Disjoint (Topology.CWComplex.closedCell m j) (Topology.CWComplex.openCell k i) := by
  rw [← Topology.CWComplex.cellFrontier_union_openCell_eq_closedCell, Set.disjoint_union_left]
  refine ⟨?_, Topology.CWComplex.disjoint_openCell_of_ne hne⟩
  obtain ⟨I, hI⟩ := Topology.CWComplex.cellFrontier_subset_finite_openCell m j
  apply Set.disjoint_left.mpr
  intro x hx hxk
  obtain ⟨l, hxl⟩ := Set.mem_iUnion.mp (hI hx)
  obtain ⟨hlm, hxl⟩ := Set.mem_iUnion.mp hxl
  obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp hxl
  obtain ⟨_, hxa⟩ := Set.mem_iUnion.mp hxa
  have hne' : (⟨l, a⟩ : Σ n, Topology.RelCWComplex.cell C n) ≠ ⟨k, i⟩ := by
    intro he
    have he' := congrArg Sigma.fst he
    exact (Nat.ne_of_lt (hlm.trans_le hm)) he'
  exact Set.disjoint_left.mp (Topology.CWComplex.disjoint_openCell_of_ne hne') hxa hxk

end HolomorphicAnosov
