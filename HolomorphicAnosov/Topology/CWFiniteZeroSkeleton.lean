import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Data.Set.Finite.Lattice

universe u
namespace HolomorphicAnosov.Topology

/-- A CW complex with finitely many zero-cells has a finite zero-skeleton.
Source: Hatcher, Algebraic Topology, Appendix p.519: the zero-skeleton is
the discrete collection of zero-cells. Each closed zero-cell is a singleton,
so the skeleton is a finite union of singleton sets. No finiteness of the
positive-dimensional cell sets is required. -/
theorem cw_finite_zero_skeleton {Z : Type u} [TopologicalSpace Z] [T2Space Z]
    [_root_.Topology.CWComplex (Set.univ : Set Z)]
    [Finite (_root_.Topology.RelCWComplex.cell (Set.univ : Set Z) 0)] :
    ((_root_.Topology.RelCWComplex.skeleton (Set.univ : Set Z) 0 : Set Z)).Finite := by
  classical
  rw [_root_.Topology.RelCWComplex.skeleton,
    _root_.Topology.RelCWComplex.coe_skeletonLT]
  simp only [Set.empty_union, zero_add]
  have heq : (⋃ (m : ℕ) (_ : (m : ℕ∞) < 1)
      (j : _root_.Topology.RelCWComplex.cell (Set.univ : Set Z) m),
      _root_.Topology.RelCWComplex.closedCell m j) =
      ⋃ j : _root_.Topology.RelCWComplex.cell (Set.univ : Set Z) 0,
      _root_.Topology.RelCWComplex.closedCell 0 j := by
    ext z
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨m, hm, j, hz⟩
      have hm0 : m = 0 := by simpa using hm
      subst m
      exact ⟨j, hz⟩
    · rintro ⟨j, hj⟩
      exact ⟨0, by simp, j, hj⟩
  rw [heq]
  apply Set.finite_iUnion
  intro j
  rw [_root_.Topology.RelCWComplex.closedCell_zero_eq_singleton]
  exact Set.finite_singleton _

end HolomorphicAnosov.Topology
