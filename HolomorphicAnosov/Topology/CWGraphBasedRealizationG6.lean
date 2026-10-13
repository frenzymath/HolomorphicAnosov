import HolomorphicAnosov.Topology.ClosedManifoldFiniteSimplicialRetractPi1FG
import HolomorphicAnosov.Topology.CWAssignedEdgeLoopsG6
import HolomorphicAnosov.Topology.CWAssignedEdgeGeneratorG6
import HolomorphicAnosov.Topology.CWTargetLoopRepresentativeG6
import HolomorphicAnosov.Topology.GraphSpanningTreeLoopRootedContractionG3

/-!
# Based realization on an original one-dimensional CW complex

Source: Hatcher, Algebraic Topology, Proposition 1B.9 pp.90–91,
Propositions 1A.1–1A.2 pp.84–85.
DAG node: `topo.cw_graph_based_realization_g6`.
-/
namespace HolomorphicAnosov
universe u v

/-- Convert the absence of original labelled cycles into the native simple-graph tree certificate.
Source: Hatcher, Algebraic Topology, Proposition 1A.1, p.84. Original labelled walks give
connectedness. A simple-graph cycle determines an original edge at each adjacency. Its distinct
unoriented edges force distinct chosen labels, and its distinct cyclic vertices force the
corresponding original vertices to be distinct. This contradicts the supplied original-cycle
exclusion. Thus the simple graph is connected and acyclic. -/
theorem labelled_cw_tree_certificate_g6
    {V E : Type*} (G : Graph V E) [G.Simple]
    (hall : G.vertexSet = Set.univ)
    (hreach : ∀ u v, ∃ n, Nonempty (CWEdgeWalk G n u v))
    (hcycles : ∀ u n, 0 < n → ∀ c : CWEdgeWalk G n u u,
      ¬(Function.Injective c.edges ∧ Function.Injective
        (fun i : Fin n ↦ c.vertices i.castSucc)))
    (r : V) : G.toSimpleGraph.IsTree := by
  classical
  have : Nonempty G.vertexSet := ⟨⟨r, hall ▸ Set.mem_univ r⟩⟩
  refine ⟨?_, ?_⟩
  · refine SimpleGraph.Connected.mk ?_
    intro u v
    obtain ⟨n, ⟨p⟩⟩ := hreach u v
    exact edgeWalk_reachable G hall p
  · intro v p hp
    have hedge : ∀ i : Fin p.length,
        ∃ e, G.IsLink e (p.getVert i.val).val (p.getVert (i.val + 1)).val := by
      intro i
      have h := p.adj_getVert_succ i.isLt
      rwa [Graph.toSimpleGraph_adj_iff] at h
    choose e he using hedge
    let c : CWEdgeWalk G p.length v.val v.val := {
      vertices := fun i ↦ (p.getVert i.val).val
      edges := e
      first := congrArg Subtype.val p.getVert_zero
      last := congrArg Subtype.val p.getVert_length
      isLink := he }
    apply hcycles v.val p.length (by have := hp.three_le_length; omega) c
    constructor
    · intro i j hij
      change e i = e j at hij
      have hs := (he i).eq_and_eq_or_eq_and_eq (hij.symm ▸ he j)
      have hs' : s(p.getVert i.val, p.getVert (i.val + 1)) =
          s(p.getVert j.val, p.getVert (j.val + 1)) := by
        apply Sym2.eq_iff.mpr
        rcases hs with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · exact Or.inl ⟨Subtype.ext h₁, Subtype.ext h₂⟩
        · exact Or.inr ⟨Subtype.ext h₁, Subtype.ext h₂⟩
      have hi : i.val < p.edges.length := by simp
      have hj : j.val < p.edges.length := by simp
      apply Fin.ext
      apply (hp.isTrail.edges_nodup.getElem_inj_iff (hi := hi) (hj := hj)).mp
      simpa only [SimpleGraph.Walk.getElem_edges] using hs'
    · intro i j hij
      apply Fin.ext
      apply hp.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; omega)
      exact Subtype.ext hij

/-- A prescribed fundamental-group homomorphism is realized on the original CW graph.
Source: Hatcher, Algebraic Topology, Proposition 1B.9, pp.90–91.

Choose the rooted original-edge spanning tree and convert its labelled cycle exclusion to
Mathlib's simple-tree certificate. Contract that very tree to the chosen root; reversing the
vertex tracks supplies rooted paths inside it. Orient every original characteristic interval.
For each edge outside the tree choose a target loop representing the homomorphism's value on
its rooted edge loop; assign constant loops to tree edges. The native one-cell adapter and
weak-CW gluing produce a continuous map, constant on every vertex. Every tree point is on a
vertex or a selected closed edge, so the map is constant on the whole tree and on all rooted
paths. The rooted-loop calculation therefore identifies each complementary generator's image
with the selected target class. Every source loop class is a finite signed word in these
original generators; homomorphisms preserve products and inverses, giving equality everywhere.
The empty complementary family yields the constant realization. Neither local finiteness nor
regularity of cells is used. -/
theorem cw_graph_based_realization_g6
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [ConnectedSpace X] [Topology.CWComplex (Set.univ : Set X)]
    (hhigh : ∀ n, IsEmpty (Topology.RelCWComplex.cell (Set.univ : Set X) (n + 2)))
    (r : Topology.RelCWComplex.cell (Set.univ : Set X) 0) (y₀ : Y)
    (φ : FundamentalGroup X (Topology.RelCWComplex.map 0 r 0) →*
      FundamentalGroup Y y₀) :
    ∃ f : C(X, Y), ∃ hf : f (Topology.RelCWComplex.map 0 r 0) = y₀,
      FundamentalGroup.mapOfEq f hf = φ := by
  classical
  let V := Topology.RelCWComplex.cell (Set.univ : Set X) 0
  let E := Topology.RelCWComplex.cell (Set.univ : Set X) 1
  let pt : V → X := fun v ↦ Topology.RelCWComplex.map 0 v 0
  obtain ⟨d, parent, treeEdge, T, _, _, hlink, hdepth, _, hall, _, hreach,
    hcycles, _, hT0, hT1, _, _, _, _, _⟩ := cw_realization_spanning_tree r
  have hsimple : ((Topology.CWComplex.OneSkeletonGraph (Set.univ : Set X)).restrict
      (T.I 1)).Simple := by
    rw [hT1]
    exact rooted_restricted_graph_simple _ r d parent treeEdge hlink hdepth
  have htree : ((Topology.CWComplex.OneSkeletonGraph (Set.univ : Set X)).restrict
      (T.I 1)).toSimpleGraph.IsTree := by
    rw [hT1]
    have : ((Topology.CWComplex.OneSkeletonGraph (Set.univ : Set X)).restrict
        (Set.range treeEdge)).Simple := hT1 ▸ hsimple
    exact labelled_cw_tree_certificate_g6 _ hall hreach hcycles r
  have hdim : ∀ n : ℕ, 1 < n → IsEmpty (Topology.RelCWComplex.cell (Set.univ : Set X) n) := by
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ n by omega)
    simpa [Nat.add_comm] using hhigh m
  have hvmem : ∀ v : V, pt v ∈ (T : Set X) := by
    intro v
    exact T.closedCell_subset_of_mem (hT0 ▸ Set.mem_univ v) ⟨0, by simp, rfl⟩
  let rootT : (T : Set X) := ⟨pt r, hvmem r⟩
  obtain ⟨H, hH0, hH1, hHr, hHmem⟩ := graph_spanning_tree_loop_rooted_contraction_g3
    hdim T hT0 hsimple htree r rootT (by change Topology.RelCWComplex.map 0 r 0 = _; congr 1; exact Subsingleton.elim _ _)
  let q : ∀ v : V, Path (pt r) (pt v) := fun v ↦ {
    toFun := fun t ↦ H (unitInterval.symm t, ⟨pt v, hvmem v⟩)
    continuous_toFun := H.continuous.comp
      (unitInterval.continuous_symm.prodMk continuous_const)
    source' := by simpa [rootT] using hH1 ⟨pt v, hvmem v⟩
    target' := by simpa using hH0 ⟨pt v, hvmem v⟩ }
  have hq : ∀ v t, q v t ∈ (T : Set X) := fun _ _ ↦ hHmem _
  have endpoints : ∀ e : E, ∃ u v : V,
      (Topology.CWComplex.OneSkeletonGraph (Set.univ : Set X)).IsLink e u v :=
    fun e ↦ Topology.CWComplex.exists_cellFrontier_one_eq e
  choose u v huv using endpoints
  have paths := fun e ↦ cw_oriented_edge_path e (u e) (v e) (huv e)
  choose σ edge hσ hedge using paths
  let rev : E → Bool := fun e ↦ decide (σ e = -1)
  have hedge' : ∀ e t, edge e t = Topology.RelCWComplex.map 1 e
      (fun _ ↦ if rev e then 1 - 2 * (t : ℝ) else 2 * (t : ℝ) - 1) := by
    intro e t
    rw [hedge]
    congr 1
    funext i
    rcases hσ e with h | h <;> norm_num [rev, h]
  let gen : E → FundamentalGroup X (pt r) := fun e ↦
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (((q (u e)).trans (edge e)).trans (q (v e)).symm))
  choose loop hloop using fun e : E ↦ cw_target_loop_representative_g6 y₀ (φ (gen e))
  let ell : E → Path y₀ y₀ := fun e ↦ if e ∈ T.I 1 then Path.refl y₀ else loop e
  obtain ⟨fsub, hfv, hfe⟩ := cw_assigned_edge_loops_g6 (Set.univ : Set X) hhigh y₀ ell rev
  let f : C(X, Y) := fsub.comp ⟨fun x ↦ ⟨x, Set.mem_univ x⟩,
    continuous_id.subtype_mk _⟩
  have hfvertex : ∀ v : V, f (pt v) = y₀ := hfv
  have hfroot : f (pt r) = y₀ := hfvertex r
  have hfonedge : ∀ e t, f (edge e t) = ell e t := by
    intro e t
    let z : Metric.closedBall (0 : Fin 1 → ℝ) 1 :=
      ⟨fun _ ↦ if rev e then 1 - 2 * (t : ℝ) else 2 * (t : ℝ) - 1, by
        rw [Metric.mem_closedBall, dist_zero_right, pi_norm_const, Real.norm_eq_abs, abs_le]
        split_ifs <;> constructor <;> linarith [t.property.1, t.property.2]⟩
    rw [hedge']
    exact hfe e t z rfl
  have hftree : ∀ x : (T : Set X), f x.val = y₀ := by
    intro x
    have hhighT : ∀ n, IsEmpty (Topology.RelCWComplex.cell (T : Set X) (n + 2)) :=
      fun n ↦ ⟨fun i ↦ (hhigh n).false i.val⟩
    rcases cw_one_dimensional_carrier_cases (T : Set X) hhighT x with
      ⟨v, hv⟩ | ⟨e, z, hz⟩
    · rw [hv]
      exact hfvertex v.val
    · obtain ⟨s, hs, _⟩ := native_one_disk_oriented_coordinate (σ e.val) (hσ e.val)
      have hzpath : Topology.RelCWComplex.map 1 e z.val = edge e.val (s z) := by
        rw [hedge, ← hs z]
        rfl
      rw [hz, hzpath, hfonedge]
      simp [ell, e.property]
  have hfq : ∀ v t, f (q v t) = y₀ := fun v t ↦ hftree ⟨_, hq v t⟩
  have hfel : ∀ e,
      ((edge e).map f.continuous).cast (hfvertex (u e)).symm (hfvertex (v e)).symm = ell e := by
    intro e
    ext t
    exact hfonedge e t
  have hcalc := cw_assigned_edge_generator_g6 f (pt r) y₀ hfroot pt q hfvertex hfq
    u v edge ell hfel
  refine ⟨f, hfroot, ?_⟩
  apply MonoidHom.ext
  intro a
  have hwords := graph_spanning_tree_loop_generation hdim T hT0 hsimple htree r
  have hz : (0 : Fin 0 → ℝ) = ![] := Subsingleton.elim _ _
  dsimp only at hwords
  rw [← hz] at hwords
  obtain ⟨word, hword⟩ := hwords u v rev edge hedge' q hq a
  rw [hword, map_list_prod, map_list_prod, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro letter _
  simp only [Function.comp_apply]
  have heq : FundamentalGroup.mapOfEq f hfroot (gen letter.1.val) = φ (gen letter.1.val) := by
    exact (hcalc letter.1.val).trans (by simpa [ell, letter.1.property] using hloop letter.1.val)
  split_ifs
  · exact heq
  · simpa only [map_inv] using congrArg Inv.inv heq



end HolomorphicAnosov
