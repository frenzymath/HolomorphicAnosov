import HolomorphicAnosov.Topology.RelativeTriangleRealization.EdgeInteriorEmbedding
import Mathlib.Topology.CWComplex.Classical.Subcomplex

noncomputable section
namespace HolomorphicAnosov.RelativeTriangleRealization

/-!
# Subcomplex packaging for the selected edge

Source: Hatcher, *Algebraic Topology*, Appendix A.2 pp.519--521. -/

/-- Closed-cell boundary data package a selected union as a classical CW
subcomplex, retaining its underlying set exactly.

For the paired-triangle quotient, the selected cells are the zero-skeleton
and one distinguished edge. The geometric proof supplies `closedCell_subset`
from the boundary stratification and `union` from the vertex/edge coverage.
Mathlib's `CWComplex.Subcomplex.mk'` performs the final packaging; this public
wrapper keeps that reusable step available to the parent construction. -/
theorem distinguishedEdgeSubcomplex_of_closedCells
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [cw : _root_.Topology.CWComplex (Set.univ : Set X)]
    (E : Set X) (I : ∀ n, Set (_root_.Topology.RelCWComplex.cell
      (Set.univ : Set X) n))
    (closedCell_subset : ∀ (n : ℕ) (i : I n),
      _root_.Topology.RelCWComplex.closedCell n i.1 ⊆ E)
    (union : (⋃ (n : ℕ) (j : I n),
      _root_.Topology.RelCWComplex.openCell n j.1) = E) :
    ∃ B : _root_.Topology.RelCWComplex.Subcomplex (Set.univ : Set X),
      (B : Set X) = E := by
  exact ⟨_root_.Topology.RelCWComplex.Subcomplex.mk'
    (Set.univ : Set X) E I closedCell_subset (by simpa only [Set.empty_union] using union), rfl⟩


end HolomorphicAnosov.RelativeTriangleRealization
