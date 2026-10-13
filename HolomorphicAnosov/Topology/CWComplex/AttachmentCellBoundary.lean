import HolomorphicAnosov.Topology.CWComplex.AttachmentCellCoverage

/-! Original cell boundaries in finite attachment towers lie in lower cells.
Source: Hatcher, Algebraic Topology, Appendix pp.519–520. -/
open Set TopCat
open scoped TopCat
universe u
namespace HolomorphicAnosov.FiniteCellAdjunction

/-- The dimension of an original cell does not exceed the last attachment stage.
Induct on the cell: zero-cells have dimension zero, retained cells keep their
old dimension, and fresh cells have the new stage dimension. -/
theorem cell_dimension_le {d n : ℕ} {X : TopCat.{u}} {T : Tower d X}
    (c : Cell T n) : n ≤ d := by
  induction c with
  | point => exact le_refl _
  | old c ih => exact Nat.le_succ_of_le ih
  | fresh => exact le_refl _

/-- The characteristic boundary of every original cell is contained in the
union of lower-dimensional original open cells. A zero-cell has empty sphere.
For an old cell, transport the preceding containment along the old inclusion.
For a fresh cell, the boundary generator identifies every boundary value with
an attaching-map value in the preceding stage; open-cell coverage there and
the dimension bound finish the argument. Hatcher Appendix pp.519–520. -/
theorem boundaryImage_subset_lower_openCells {d n : ℕ} {X : TopCat.{u}}
    {T : Tower d X} (c : Cell T n) :
    boundaryImage c ⊆ ⋃ (m : ℕ) (_ : m < n) (b : Cell T m), openCell b := by
  induction c with
  | point x =>
    rintro y ⟨z, rfl⟩
    have hz := z.down.property
    have heq : z.down.val = 0 := Subsingleton.elim _ _
    simp [heq] at hz
  | old c ih =>
    rintro y ⟨z, rfl⟩
    obtain ⟨m, hmn, b, v, hv⟩ := mem_iUnion.mp (ih ⟨z, rfl⟩) |>.imp fun m h ↦
      by simpa only [mem_iUnion, openCell, mem_range] using h
    exact mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨hmn,
      mem_iUnion.mpr ⟨.old b, v, congrArg oldInclusion hv⟩⟩⟩
  | @fresh d X T k a i =>
    rintro y ⟨z, rfl⟩
    have hz : a i z ∈ ⋃ (m : ℕ) (b : Cell T m), openCell b := by
      rw [tower_openCell_cover T]
      exact mem_univ _
    obtain ⟨m, b, v, hv⟩ := mem_iUnion.mp hz |>.imp fun m h ↦
      by simpa only [mem_iUnion, openCell, mem_range] using h
    refine mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨Nat.lt_succ_of_le (cell_dimension_le b),
      mem_iUnion.mpr ⟨.old b, v, ?_⟩⟩⟩
    exact (congrArg oldInclusion hv).trans (newCharacteristic_boundary i z).symm

end HolomorphicAnosov.FiniteCellAdjunction
