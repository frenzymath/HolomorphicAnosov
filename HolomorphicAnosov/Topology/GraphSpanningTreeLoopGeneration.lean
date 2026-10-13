import HolomorphicAnosov.Topology.GraphTreeUniquePathG3
import HolomorphicAnosov.Topology.GraphSpanningTreeLoopSubgroupClosure
import HolomorphicAnosov.Topology.CWRootedContractionCollapse
import HolomorphicAnosov.Topology.CWGraphCollapsePresentation
import HolomorphicAnosov.Topology.RootedLabelledTree
import HolomorphicAnosov.Topology.CWComplex.HomotopyExtension
import HolomorphicAnosov.Topology.OpenCoverPathSubdivision
import HolomorphicAnosov.Topology.TorusStandardWinding
import Mathlib.Topology.CWComplex.Classical.Graph
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Combinatorics.Graph.Simple
import Mathlib.Combinatorics.Graph.Delete
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# Generators of the fundamental group of a CW graph

Source: Hatcher, *Algebraic Topology*, pp.83–85, especially Proposition 1A.2,
with Propositions 0.16–0.17, pp.15–16, Lemma 1.15, p.35, and Example 1.21,
pp.43–44. DAG node: `topo.graph_spanning_tree_loop_generation`.

The tree is an actual CW subcomplex. Only its restricted incidence graph is required
to be simple and a tree; the original graph can have loops and parallel labelled edges.
Characteristic edge paths are specified by their exact affine parametrizations.
-/

open _root_.Topology

namespace HolomorphicAnosov

/-- The original non-tree edge loops generate the actual based fundamental group.

Source: Hatcher, *Algebraic Topology*, graph topology p.83, rooted contraction
Proposition 1A.1 p.84, and Proposition 1A.2 pp.84–85; Propositions 0.16–0.17
pp.15–16, Lemma 1.15 p.35, Example 1.21/Theorem 1.20 pp.43–44, and circle
winding Theorem 1.7 pp.29–31 supply the expanded generation proof below.

The native graph `Simple` condition excludes loops and parallel edges only inside T.
Together with `IsTree` this is precisely connectedness and acyclicity of its original
edge-labelled graph. The full CW graph and its cell-index types need not be finite,
countable, or locally finite. Root paths may be any paths inside T: their endpoint-fixed
homotopy classes equal those of the unique finite tree edge paths, so this expresses
the same specified rooted generators independently of their parametrization.

Proof: Connectedness and acyclicity give the unique finite edge path from the root to
each tree vertex. Assign each vertex its path length from the root. Each nonroot vertex
has exactly one edge to the preceding layer; every tree edge is one of these edges,
since any additional edge would close a cycle. Apply Hatcher's rooted contraction:
collapse edges of depth d toward their predecessors during [2^(-d),2^(-d+1)], fixing
lower layers, and use the identity at time zero. On each closed characteristic interval
only its finite root path is traversed, giving a finite concatenation of continuous
linear formulas with an initial stationary interval. The formulas agree at endpoints.
Closed pasting gives continuity on each characteristic cylinder. The characteristic
disjoint-union quotient, and product descent with the locally compact time interval,
give a jointly continuous contraction of T fixing the root. Thus any two root paths
with the same endpoint are homotopic relative endpoints inside T; in particular the
given q paths represent the unique finite tree paths.

By the CW homotopy extension property 0.16, extend this rooted contraction to a homotopy
F of the whole graph starting at its identity. It preserves T and fixes the root.
At time one it factors through the quotient Q = X/T, giving a based map r:Q→X.
The homotopy qF also factors jointly through the quotient, by the same interval-product
descent, and shows qr homotopic to the identity of Q, while F shows rq homotopic to the
identity of X. Both homotopies fix the basepoint. Therefore the induced based
fundamental-group maps are inverse isomorphisms, as in Proposition 0.17.

The quotient has one vertex and one circle for each original edge outside T. Its
topology is the weak CW wedge topology, obtained by attaching all those characteristic
intervals with both ends at the vertex. Use Example 1.21's open sets consisting of the
whole vertex collar and of one circle together with collars on every other circle.
A loop's compact parameter interval admits a finite subordinate subdivision, by
Lemma 1.15. Insert paths in the collar from the vertex to its finitely many subdivision
junctions, followed by their reverses. These cancellations express its class as a
finite product of loops in the specified circle neighborhoods. Contract each extra
collar to the vertex. Theorem 1.7 identifies the remaining based circle loop with an
integer power of its once-around oriented characteristic loop. Hence the circle loops
and their inverses generate the quotient's fundamental group even for an infinite wedge.

For each oriented original non-tree edge e:u→v, the quotient sends q_u followed by its
characteristic traversal followed by reverse(q_v) to precisely that oriented circle
loop: both root paths become constant. Unit and associativity laws in the path-homotopy
quotient give equality of these classes without a basepoint conjugation. Express the
image of any original loop class as the finite word just obtained and use injectivity
of the quotient-induced isomorphism to pull back that same word. The displayed list
records generators and inverses explicitly. Reversed group composition conventions
only reverse the finite list and do not change generation.

If there are no non-tree edges, Q is a point and its fundamental group is trivial, so
the empty list suffices. This covers a single-vertex graph. Loop edges and parallel
edges outside T remain distinct original labels and distinct generator indices. No
freeness assertion, finiteness restriction, or extra topological hypothesis is used.
-/
theorem graph_spanning_tree_loop_generation
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [CWComplex (Set.univ : Set X)]
    (hdim : ∀ n : ℕ, 1 < n → IsEmpty (RelCWComplex.cell (Set.univ : Set X) n))
    (T : RelCWComplex.Subcomplex (Set.univ : Set X))
    (hT0 : T.I 0 = Set.univ)
    (hTsimple : ((CWComplex.OneSkeletonGraph (Set.univ : Set X)).restrict (T.I 1)).Simple)
    (hTtree :
      ((CWComplex.OneSkeletonGraph (Set.univ : Set X)).restrict (T.I 1)).toSimpleGraph.IsTree)
    (v0 : RelCWComplex.cell (Set.univ : Set X) 0) :
    let pt := fun v : RelCWComplex.cell (Set.univ : Set X) 0 ↦
      RelCWComplex.map (C := Set.univ) 0 v ![]
    ∀ (u v : RelCWComplex.cell (Set.univ : Set X) 1 →
        RelCWComplex.cell (Set.univ : Set X) 0)
      (rev : RelCWComplex.cell (Set.univ : Set X) 1 → Bool)
      (edgePath : ∀ e, Path (pt (u e)) (pt (v e))),
      (∀ e t, edgePath e t = RelCWComplex.map (C := Set.univ) 1 e
        (fun _ ↦ if rev e then 1 - 2 * (t : ℝ) else 2 * (t : ℝ) - 1)) →
      ∀ (q : ∀ w, Path (pt v0) (pt w)),
        (∀ w t, q w t ∈ (T : Set X)) →
        let generator : {e : RelCWComplex.cell (Set.univ : Set X) 1 // e ∉ T.I 1} →
            FundamentalGroup X (pt v0) := fun e ↦
          FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
            (((q (u e)).trans (edgePath e)).trans (q (v e)).symm))
        ∀ α : FundamentalGroup X (pt v0),
          ∃ word : List ({e : RelCWComplex.cell (Set.univ : Set X) 1 // e ∉ T.I 1} × Bool),
            α = (word.map (fun letter ↦
              if letter.2 then generator letter.1 else (generator letter.1)⁻¹)).prod := by
  dsimp
  intro u v rev edgePath hedge q hq α
  let generator : {e : RelCWComplex.cell (Set.univ : Set X) 1 // e ∉ T.I 1} →
      FundamentalGroup X (RelCWComplex.map (C := Set.univ) 0 v0 ![]) := fun e ↦
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (((q (u e)).trans (edgePath e)).trans (q (v e)).symm))
  have hα : α ∈ Subgroup.closure (Set.range generator) := by
    exact graph_spanning_tree_loop_subgroup_closure hdim T hT0 hTsimple hTtree v0
      u v rev edgePath hedge q hq α
  exact Topology.exists_signed_word_of_mem_subgroup_closure generator hα

end HolomorphicAnosov
