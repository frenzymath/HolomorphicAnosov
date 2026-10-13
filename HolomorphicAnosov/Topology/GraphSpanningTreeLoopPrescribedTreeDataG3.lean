import HolomorphicAnosov.Topology.RootedLabelledTree
import Mathlib.Topology.CWComplex.Classical.Graph
import Mathlib.Combinatorics.Graph.Simple
import Mathlib.Combinatorics.Graph.Delete
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace HolomorphicAnosov

open _root_.Topology

/-- Extract the rooted parent-edge data from the prescribed CW subcomplex.

Source: Hatcher, *Algebraic Topology*, Proposition 1A.1 p.84.  The restricted
one-skeleton has the literal CW zero-cells as vertices and the tree's selected
one-cells as edges.  `rooted_labelled_tree_data` supplies the unique parent,
depth, and edge bijection; the equalities `hT0` and the restriction edge set
reindex those data to the actual cells of `T`.  This provider records exactly
the reindexing obligation used by the contraction theorem.
-/
theorem graph_spanning_tree_loop_prescribed_tree_data_g3
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [Topology.CWComplex (Set.univ : Set X)]
    (T : Topology.RelCWComplex.Subcomplex (Set.univ : Set X))
    (_hT0 : T.I 0 = Set.univ)
    (hTsimple : ((Topology.CWComplex.OneSkeletonGraph (Set.univ : Set X)).restrict (T.I 1)).Simple)
    (hTtree :
      ((Topology.CWComplex.OneSkeletonGraph (Set.univ : Set X)).restrict (T.I 1)).toSimpleGraph.IsTree)
    (v0 : Topology.RelCWComplex.cell (Set.univ : Set X) 0) :
    let G := (Topology.CWComplex.OneSkeletonGraph (Set.univ : Set X)).restrict (T.I 1)
    ∃ (d : G.vertexSet → ℕ)
      (parent : {v : G.vertexSet // v ≠ ⟨v0, by trivial⟩} → G.vertexSet)
      (edge : {v : G.vertexSet // v ≠ ⟨v0, by trivial⟩} ≃ G.edgeSet),
      d ⟨v0, by trivial⟩ = 0 ∧
      (∀ v, d (parent v) + 1 = d v.val) ∧
      (∀ v, G.IsLink (edge v).val (parent v).val v.val) := by
  dsimp
  exact rooted_labelled_tree_data
    ((Topology.CWComplex.OneSkeletonGraph (Set.univ : Set X)).restrict (T.I 1))
    hTtree ⟨v0, by trivial⟩

end HolomorphicAnosov
