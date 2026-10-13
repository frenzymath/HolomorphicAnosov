import HolomorphicAnosov.Topology.CWComplex.CompactGenerationAmbient
import HolomorphicAnosov.Topology.CWComplex.CompactGenerationClosedSubtype
import Mathlib.Topology.CWComplex.Classical.Basic

/-!
# Compact generation for CW complexes and their native subspaces

Source: Hatcher, *Algebraic Topology*, Appendix, pp.521 and 523, the closed-cell
compact-test argument; Fritsch–Piccinini, *Cellular Structures in Topology*,
Appendix A.1, p.242, closed-subspace inheritance of the k-space property.

DAG node: `topo.cw_subspaces_compact_generation_g8`.
The subtype carriers below retain the topology induced by the given ambient space.
-/

namespace HolomorphicAnosov.Topology.CWComplex

universe u

/-- A Hausdorff classical CW complex, all its native subcomplexes, and all its
finite-dimensional skeleta are compactly generated in their given topologies.

Source: Hatcher, *Algebraic Topology*, Appendix pp.521 and 523, together with
Fritsch–Piccinini, *Cellular Structures in Topology*, Appendix A.1, p.242.

Proof: apply `compactlyGeneratedSpace_of_cw` to the ambient CW complex. Its
closed-cell proof tests closedness on compact closed cells, whose topology detects
closed subsets of the complex. Install the resulting compact-generation instance
on the ambient space. For each native subcomplex A, the projection `A.closed`
states that its carrier is closed. Apply
`compactlyGeneratedSpace_of_closed_subtype` to that carrier. The native skeleton
of index n is itself a subcomplex, so the same closed-subtype theorem applies to
its carrier. The skeleton index is n (cells through dimension n), not skeletonLT n.
No finite-cell or local-finiteness assumption is used. The empty complex, empty
subcomplex, and zero-skeleton are included. No topology is replaced by a
compactly generated modification.

This proof retains the existing node statement exactly. Both non-Mathlib
prerequisites are imported above. -/
theorem compactlyGeneratedSpace_of_cw_subspaces
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)] :
    CompactlyGeneratedSpace X ∧
      (∀ A : _root_.Topology.RelCWComplex.Subcomplex (Set.univ : Set X),
        CompactlyGeneratedSpace (A : Set X)) ∧
      (∀ n : ℕ,
        CompactlyGeneratedSpace
          (_root_.Topology.RelCWComplex.skeleton (Set.univ : Set X) (n : ℕ∞) : Set X)) := by
  have hX : CompactlyGeneratedSpace X := compactlyGeneratedSpace_of_cw
  let : CompactlyGeneratedSpace X := hX
  refine ⟨hX, ?_, ?_⟩
  · intro A
    exact compactlyGeneratedSpace_of_closed_subtype A.closed
  · intro n
    exact compactlyGeneratedSpace_of_closed_subtype
      (_root_.Topology.RelCWComplex.skeleton (Set.univ : Set X) (n : ℕ∞)).closed

end HolomorphicAnosov.Topology.CWComplex

