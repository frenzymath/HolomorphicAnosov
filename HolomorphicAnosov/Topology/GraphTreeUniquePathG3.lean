import Mathlib.Combinatorics.Graph.Simple
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace HolomorphicAnosov

/-- A rooted labelled simple tree has a unique finite simple walk to the root.

Source: Hatcher, *Algebraic Topology*, Proposition 1A.1, p.84, together with
pinned Mathlib `SimpleGraph.IsTree.existsUnique_path` in
`Mathlib/Combinatorics/SimpleGraph/Acyclic.lean`. This interface isolates the
cycle argument used by the rooted contraction: acyclicity rules out a second
simple root path, while connectedness supplies one. No finiteness or topology
hypothesis is used.
-/
theorem graph_tree_unique_path_g3
    {V E : Type*} (G : Graph V E) [G.Simple]
    (hG : G.toSimpleGraph.IsTree) (r v : G.vertexSet) :
    ∃! p : G.toSimpleGraph.Walk v r, p.IsPath := by
  exact hG.existsUnique_path v r

end HolomorphicAnosov
