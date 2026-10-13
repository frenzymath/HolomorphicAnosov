import HolomorphicAnosov.Topology.CWRootedContractionCollapse
import HolomorphicAnosov.Topology.GraphSpanningTreeLoopRootedContractionG3
import HolomorphicAnosov.Topology.GraphSpanningTreeLoopRootedHomotopyRelG3
import HolomorphicAnosov.Topology.GraphSpanningTreeLoopFundamentalMapHomotopyG3
import HolomorphicAnosov.Topology.GraphSpanningTreeLoopFundamentalMapInjectiveG3
import HolomorphicAnosov.Topology.GraphSpanningTreeLoopFundamentalMapHomotopyG3
import Mathlib.Topology.CWComplex.Classical.Graph
import Mathlib.Combinatorics.Graph.Simple
import Mathlib.Combinatorics.Graph.Delete
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

namespace HolomorphicAnosov

open _root_.Topology

/-- The rooted tree collapse induces an injective map on the based fundamental
 group. This is the first geometric residual in the spanning-tree quotient
 proof.

Source: Hatcher, *Algebraic Topology*, Proposition 1A.1, p.84, together with
Propositions 0.16--0.17, pp.15--16. The rooted contraction of the spanning
 tree fixes the chosen root and supplies a based homotopy inverse to the
 collapse; the induced fundamental-group map is therefore injective. The
 proof remains a named residual until the contraction is assembled from the
 current CW interfaces.
-/
theorem graph_spanning_tree_loop_compact_subdivision_quotient_injective_g3
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [CWComplex (Set.univ : Set X)]
    (hdim : ∀ n : ℕ, 1 < n → IsEmpty (RelCWComplex.cell (Set.univ : Set X) n))
    (T : RelCWComplex.Subcomplex (Set.univ : Set X))
    (hT0 : T.I 0 = Set.univ)
    (hTsimple : ((CWComplex.OneSkeletonGraph (Set.univ : Set X)).restrict (T.I 1)).Simple)
    (hTtree :
      ((CWComplex.OneSkeletonGraph (Set.univ : Set X)).restrict (T.I 1)).toSimpleGraph.IsTree)
    (v0 : RelCWComplex.cell (Set.univ : Set X) 0) :
    Function.Injective (FundamentalGroup.map (GoodPair.collapse (T : Set X))
      (RelCWComplex.map (C := Set.univ) 0 v0 ![]))  := by
  let r0 : (T : Set X) := ⟨Topology.RelCWComplex.map (C := Set.univ) 0 v0 ![], by
    apply T.closedCell_subset_of_mem (n := 0) (i := v0) (by rw [hT0]; trivial)
    exact ⟨(![] : Fin 0 → ℝ), by simp, rfl⟩⟩
  have hr0 : r0.val = Topology.RelCWComplex.map (C := Set.univ) 0 v0 ![] := rfl
  obtain ⟨H, hzero, hone, hroot, hmem⟩ :=
    graph_spanning_tree_loop_rooted_contraction_g3
      hdim T hT0 hTsimple hTtree v0 r0 hr0
  let Crel := graph_spanning_tree_loop_rooted_homotopy_rel_g3
      (T : Set X) r0 H hzero hone hroot hmem
  obtain ⟨r, hr, hleft, _hright⟩ :=
    Topology.cw_rooted_contraction_collapse_inverse T r0 Crel
  let ψ : FundamentalGroup (GoodPair.Collapsed (T : Set X))
      (GoodPair.collapse (T : Set X) r0.val) →*
      FundamentalGroup X r0.val := FundamentalGroup.mapOfEq r hr
  let φ : FundamentalGroup X r0.val →*
      FundamentalGroup (GoodPair.Collapsed (T : Set X))
        (GoodPair.collapse (T : Set X) r0.val) :=
    FundamentalGroup.map (GoodPair.collapse (T : Set X)) r0.val
  have hmap : FundamentalGroup.mapOfEq (ContinuousMap.id X) rfl =
      FundamentalGroup.mapOfEq (r.comp (GoodPair.collapse (T : Set X))) hr := by
    obtain ⟨Hleft⟩ := hleft
    exact graph_spanning_tree_loop_fundamental_map_homotopy_g3
      r0.val r0.val (ContinuousMap.id X)
      (r.comp (GoodPair.collapse (T : Set X))) rfl hr Hleft
  have hcomp : ψ.comp φ = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro α
    have hcompα : ψ (φ α) =
        FundamentalGroup.mapOfEq (r.comp (GoodPair.collapse (T : Set X))) hr α := by
      refine Quotient.inductionOn α ?_
      intro p
      change FundamentalGroup.mapOfEq r hr
        (FundamentalGroup.map (GoodPair.collapse (T : Set X)) r0.val
          (FundamentalGroup.fromPath ⟦p⟧)) =
        FundamentalGroup.mapOfEq (r.comp (GoodPair.collapse (T : Set X))) hr
          (FundamentalGroup.fromPath ⟦p⟧)
      rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply]
      rfl
    have hid : FundamentalGroup.mapOfEq (ContinuousMap.id X) rfl α = α := by
      refine Quotient.inductionOn α ?_
      intro p
      change FundamentalGroup.mapOfEq (ContinuousMap.id X) rfl
          (FundamentalGroup.fromPath ⟦p⟧) = FundamentalGroup.fromPath ⟦p⟧
      rw [FundamentalGroup.mapOfEq_apply]
      change Path.Homotopic.Quotient.mk (p.map continuous_id) =
        Path.Homotopic.Quotient.mk p
      rw [Path.map_id]
    change ψ (φ α) = α
    rw [hcompα, ← hmap]
    exact hid
  exact Topology.graph_spanning_tree_loop_fundamental_map_injective_of_left_inverse_g3 φ ψ hcomp


end HolomorphicAnosov
