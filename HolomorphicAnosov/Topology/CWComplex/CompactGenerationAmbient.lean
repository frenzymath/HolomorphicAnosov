import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace

/-! Source: Hatcher, Algebraic Topology, Appendix p.523, the closed-cell compact-generation
argument. DAG: topo.cw_compact_generation_g8. -/

namespace HolomorphicAnosov.Topology.CWComplex

universe u

/--
A Hausdorff classical CW complex is compactly generated in its supplied topology.

For a set `s`, Mathlib's CW closed-set criterion reduces closedness to the
intersections with closed cells. Each closed cell is compact because the
characteristic map is continuous on the compact closed disk. Thus the
`compactlyGeneratedSpace_of_isClosed_of_t2` constructor applies directly.
This is the closed-cell generation argument from Hatcher p. 523 and does not
construct a new topology or assume normality.
-/
theorem compactlyGeneratedSpace_of_cw
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)] : CompactlyGeneratedSpace X := by
  apply compactlyGeneratedSpace_of_isClosed_of_t2
  intro s hs
  apply (_root_.Topology.CWComplex.closed (Set.univ : Set X) s (Set.subset_univ s)).2
  intro n j
  exact hs _ (_root_.Topology.CWComplex.isCompact_closedCell
    (C := (Set.univ : Set X)) (n := n) (i := j))

end HolomorphicAnosov.Topology.CWComplex

