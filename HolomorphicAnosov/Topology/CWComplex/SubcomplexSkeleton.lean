import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.CWComplex.Classical.Subcomplex

namespace HolomorphicAnosov

/-- The skeleton of a subcomplex is its intersection with the ambient
skeleton. Source: Hatcher, Algebraic Topology, section 0, CW subcomplexes;
the explicit membership proof is agent-written. A point of either skeleton
belongs to an open cell of bounded dimension. A cell meeting a subcomplex
belongs to that subcomplex, since every omitted open cell is disjoint from
it. Thus the same cell represents the point on both sides. -/
theorem cw_subcomplex_skeleton
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (C : Set X) [Topology.CWComplex C]
    (W : Topology.CWComplex.Subcomplex C) (n : ℕ∞) :
    (Topology.CWComplex.skeleton (W : Set X) n : Set X) =
      (W : Set X) ∩ (Topology.CWComplex.skeleton C n : Set X) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨m, hm, j, hj⟩ := Topology.CWComplex.mem_skeleton_iff.mp hx
    exact ⟨W.openCell_subset_of_mem j.property hj,
      Topology.CWComplex.mem_skeleton_iff.mpr ⟨m, hm, j.val, hj⟩⟩
  · rintro ⟨hxW, hx⟩
    obtain ⟨m, hm, j, hj⟩ := Topology.CWComplex.mem_skeleton_iff.mp hx
    have hjW : j ∈ W.I m := by
      by_contra h
      exact Set.disjoint_left.mp (W.disjoint_openCell_subcomplex_of_not_mem h) hj hxW
    exact Topology.CWComplex.mem_skeleton_iff.mpr ⟨m, hm, ⟨j, hjW⟩, hj⟩

end HolomorphicAnosov
