import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.UnitInterval

open Set _root_.Topology
namespace HolomorphicAnosov.Topology

/-- Endpoint copies and open prisms over the original open cells cover the
ordinary product with the unit interval.

Source: Fritsch–Piccinini, *Cellular Structures in Topology*, Theorem 2.2.2,
p.58: the product open cells are endpoint copies and open products with the
interval one-cell. This is the set-level coverage part of the written
multiplication/addition construction, before packaging a new CW structure.

Proof: Mathlib's original open-cell coverage supplies a cell containing the
first coordinate. The interval subtype has exactly three disjoint cases:
`0`, `1`, and the open one-cell `(0,1)`. Place the pair in the corresponding
endpoint or prism product. Conversely each displayed product is contained in
the ambient product. No finiteness, regularity, or product CW instance is
assumed. -/
theorem endpoint_prism_open_cover
    {X : Type*} [TopologicalSpace X] [CWComplex (univ : Set X)] :
    (⋃ (n : ℕ) (i : RelCWComplex.cell (univ : Set X) n) (a : Bool),
      (CWComplex.openCell (C := (univ : Set X)) n i).prod
        {if a then (1 : unitInterval) else 0}) ∪
      (⋃ (d : ℕ) (i : RelCWComplex.cell (univ : Set X) d),
        (CWComplex.openCell (C := (univ : Set X)) d i).prod
          (Ioo (0 : unitInterval) 1)) =
      (univ : Set X).prod (univ : Set unitInterval) := by
  ext y
  constructor
  · intro hy
    rcases hy with hy | hy
    · simp only [mem_iUnion] at hy
      rcases hy with ⟨n, i, a, ⟨hx, ht⟩⟩
      exact ⟨mem_univ _, mem_univ _⟩
    · simp only [mem_iUnion] at hy
      rcases hy with ⟨d, i, ⟨hx, ht⟩⟩
      exact ⟨mem_univ _, mem_univ _⟩
  · rintro ⟨hx, ht⟩
    have hcell : y.1 ∈ ⋃ (n : ℕ) (i : RelCWComplex.cell (univ : Set X) n),
        CWComplex.openCell (C := (univ : Set X)) n i := by
      rw [CWComplex.iUnion_openCell_eq_complex]
      exact mem_univ _
    rcases mem_iUnion.mp hcell with ⟨n, hcell⟩
    rcases mem_iUnion.mp hcell with ⟨i, hi⟩
    by_cases h0 : (y.2 : ℝ) = 0
    · left
      refine mem_iUnion_of_mem n (mem_iUnion_of_mem i (mem_iUnion_of_mem false ?_))
      exact ⟨hi, by apply Subtype.ext; exact h0⟩
    by_cases h1 : (y.2 : ℝ) = 1
    · left
      refine mem_iUnion_of_mem n (mem_iUnion_of_mem i (mem_iUnion_of_mem true ?_))
      exact ⟨hi, by apply Subtype.ext; exact h1⟩
    · right
      refine mem_iUnion_of_mem n (mem_iUnion_of_mem i ?_)
      have ht0 : (0 : ℝ) < y.2 := by
        have hy0 : (0 : ℝ) ≤ y.2 := y.2.property.1
        exact lt_of_le_of_ne hy0 (Ne.symm h0)
      have ht1 : (y.2 : ℝ) < 1 := by
        have hy1 : (y.2 : ℝ) ≤ 1 := y.2.property.2
        exact lt_of_le_of_ne hy1 h1
      exact ⟨hi, ht0, ht1⟩

end HolomorphicAnosov.Topology

