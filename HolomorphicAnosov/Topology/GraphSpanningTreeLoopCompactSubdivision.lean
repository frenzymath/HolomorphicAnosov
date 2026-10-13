import HolomorphicAnosov.Topology.GraphSpanningTreeLoopCompactSubdivisionNonemptySubgroupG3
import HolomorphicAnosov.Topology.GraphSpanningTreeLoopQuotientInjectiveG3
import HolomorphicAnosov.Topology.GraphSpanningTreeLoopConstantCollapseG3
import HolomorphicAnosov.Topology.GraphSpanningTreeLoopSubdivisionDataG3
import Mathlib.Topology.CWComplex.Classical.Graph
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Combinatorics.Graph.Simple
import Mathlib.Combinatorics.Graph.Delete
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

open _root_.Topology

namespace HolomorphicAnosov

/--
The compact-loop and weak-wedge stage in Hatcher's spanning-tree argument.

Source: Hatcher, *Algebraic Topology*, Proposition 1A.2, pp. 84--85,
using Proposition 1A.1, p. 84, and the quotient description on p. 83.
The rooted tree is first contracted relative to its root and the homotopy
extension theorem identifies the based fundamental group with that of the
quotient.  The quotient is the weak wedge of the characteristic circles
indexed by the edges outside the tree.  A loop has compact image, so the
open-cover subdivision lemma gives a finite subdivision subordinate to the
vertex collar and circle neighborhoods.  Cancelling the collar paths leaves
a finite product of circle loops and inverses; winding on each circle changes
that product to a finite product of the oriented characteristic loops.  The
quotient map sends the specified rooted characteristic loop to the
corresponding circle loop, and the induced fundamental-group isomorphism
pulls the finite product back to the original graph.  The empty complement
case is the trivial group.  The proof is intentionally retained as a named
admission until the quotient descent and finite-subdivision maps are written
out against the current Mathlib CW interfaces.
-/
theorem graph_spanning_tree_loop_compact_subdivision
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
          α ∈ Subgroup.closure (Set.range generator) := by
  dsimp
  intro u v rev edgePath hedge q hq α
  let pt := fun w : RelCWComplex.cell (Set.univ : Set X) 0 ↦
    RelCWComplex.map (C := Set.univ) 0 w ![]
  let E := {e : RelCWComplex.cell (Set.univ : Set X) 1 // e ∉ T.I 1}
  let generator : E → FundamentalGroup X (pt v0) := fun e ↦
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (((q (u e)).trans (edgePath e)).trans (q (v e)).symm))
  classical
  by_cases hE : ∃ e : RelCWComplex.cell (Set.univ : Set X) 1, e ∉ T.I 1
  · exact graph_spanning_tree_loop_compact_subdivision_nonempty_subgroup_g3
      hdim T hT0 hTsimple hTtree v0 u v rev edgePath hedge q hq hE α
  · have hfull : ∀ e : RelCWComplex.cell (Set.univ : Set X) 1, e ∈ T.I 1 := by
      intro e
      by_contra he
      exact hE ⟨e, he⟩
    have hcarrier : ∀ x : X, x ∈ (T : Set X) := by
      intro x
      have hx : x ∈ ⋃ (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) n),
          RelCWComplex.closedCell n i := by
        rw [CWComplex.union]
        trivial
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hn
      cases n with
      | zero => exact T.closedCell_subset_of_mem (by rw [hT0]; trivial) hi
      | succ n =>
          cases n with
          | zero => exact T.closedCell_subset_of_mem (hfull i) hi
          | succ n => exact False.elim ((hdim (n + 2) (by omega)).false i)
    let Q := GoodPair.collapse (T : Set X)
    have hmapone : FundamentalGroup.map Q (pt v0) α = 1 := by
      refine Quotient.inductionOn α ?_
      intro p
      simpa [Q] using graph_spanning_tree_loop_constant_collapse_g3 Q (pt v0) p
        (fun t ↦ Quotient.sound (Or.inr ⟨hcarrier _, hcarrier _⟩))
    have hinj : Function.Injective (FundamentalGroup.map Q (pt v0)) := by
      exact graph_spanning_tree_loop_compact_subdivision_quotient_injective_g3
        hdim T hT0 hTsimple hTtree v0
    have haone : α = 1 := by
      apply hinj
      rw [hmapone]
      rfl
    rw [haone]
    exact Subgroup.one_mem _

end HolomorphicAnosov
