import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace HolomorphicAnosov

open Set Topology _root_.Topology

/-- Cells contained in a small ball cover a smaller punctured ball.

Source: Hatcher, Algebraic Topology, Theorem A.7, printed p.526, the assertion
that the small-cell union together with the compact carrier is a neighborhood
of its center. For a point of the smaller ball outside the carrier, choose an
open cell containing it. The corresponding closed cell meets the smaller ball,
so the shrinking hypothesis puts the entire closed cell in the prescribed
larger ball. No assertion that this union is a subcomplex is needed here. -/
theorem hatcher_shrinking_cells_neighborhood
    {E : Type*} [MetricSpace E] (C : Set E)
    [CWComplex (univ : Set {x : E // x ∉ C})]
    (c : E) (ε : ℝ) (hε : 0 < ε)
    (hshrink : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (d : ℕ) (i : RelCWComplex.cell (univ : Set {x : E // x ∉ C}) d),
        (∃ x : {x : E // x ∉ C},
          x ∈ RelCWComplex.closedCell (C := univ) d i ∧ dist x.val c < δ) →
        ∀ x : {x : E // x ∉ C},
          x ∈ RelCWComplex.closedCell (C := univ) d i → dist x.val c < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Metric.ball c δ,
      x ∈ C ∨ ∃ (y : {x : E // x ∉ C}) (d : ℕ)
        (i : RelCWComplex.cell (univ : Set {x : E // x ∉ C}) d),
        y.val = x ∧ y ∈ RelCWComplex.closedCell (C := univ) d i ∧
          ∀ z : {x : E // x ∉ C},
            z ∈ RelCWComplex.closedCell (C := univ) d i → dist z.val c < ε := by
  classical
  obtain ⟨δ, hδ, hsmall⟩ := hshrink ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  by_cases hxc : x ∈ C
  · exact Or.inl hxc
  · let y : {x : E // x ∉ C} := ⟨x, hxc⟩
    have hy : y ∈ ⋃ d, ⋃ i, RelCWComplex.openCell
        (C := (univ : Set {x : E // x ∉ C})) d i := by
      rw [CWComplex.iUnion_openCell_eq_complex]
      exact mem_univ y
    obtain ⟨d, i, hi⟩ := mem_iUnion₂.mp hy
    have hclosed := RelCWComplex.openCell_subset_closedCell d i hi
    exact Or.inr ⟨y, d, i, rfl, hclosed, hsmall d i ⟨y, hclosed, hx⟩⟩


end HolomorphicAnosov
