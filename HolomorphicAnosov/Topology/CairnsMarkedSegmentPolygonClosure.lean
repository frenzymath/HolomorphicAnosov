import HolomorphicAnosov.Topology.SegmentChainPolygonClosure
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Polygon.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Connected.LocallyConnected
import HolomorphicAnosov.Topology.OpenConnectedSegmentChain
import Mathlib.Analysis.Convex.Topology
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Analysis.Convex.Between

/-!
# Polygon closure retaining a marked transverse crossing

This module formalizes `topo.cairns_marked_segment_polygon_closure`. The plane is
`ℂ` with its real vector-space structure. All segments and affine lines are over
`ℝ`; no complex-affine-line meaning is intended.

Source context: S. S. Cairns, *An Elementary Proof of the Jordan-Schoenflies
Theorem* (1951), Lemma 3.1(B,C), printed pp. 861–862. The arbitrary compact-obstacle
marked-edge closure argument is the explicitly agent-written omitted-step proof
in the current DAG, rather than a claim that Cairns supplies this full variant.
-/

namespace HolomorphicAnosov

open Set

/-- A transverse segment whose endpoints lie in one connected complementary
component can be closed to a simple polygon while retaining its marked crossing.

A simple closed polygon is represented by Mathlib's cyclic finite `Polygon`,
with at least three vertices, injective vertices, nondegenerate edges, and exact
pairwise edge-intersection conditions. Distinct edges may meet only in their
common endpoints. No convexity, noncollinear-triples or general-position
requirement is imposed. `Polygon.boundary ℝ` is the actual union of these closed
edges. Thus the result does not use an opaque polygon predicate.

The component hypothesis is membership in the actual `connectedComponentIn`
of the open complement, not path-component membership. The compact obstacle may
meet the long segment away from the marked stub, including at either endpoint.
The marked point is strictly between both input endpoint pairs and strictly
between the endpoints of the output edge, which lies on the original stub line.

Source and provenance: Cairns (1951), Lemma 3.1(B) last paragraph and part (C),
printed pp. 861–862, supplies the polygon-pasting context. The following complete
natural-language proof is the agent-written omission expansion recorded in the
matching DAG node. Its abstract shortest-path existence and minimality are Mathlib theorems.

M1. In the common open connected component U of ℝ²\(K∪d), let R be the points reachable from x_- by
finite straight-segment chains in U. Every point of U has a small convex ball contained in U.
Such a ball around a point of R extends its chain, whereas a ball around a point outside R
cannot meet R, or a segment in that ball would extend a chain to the point. Hence R and U\R are
relatively open; connectedness forces R=U. There is therefore a finite polygonal chain q from
x_- to x_+ missing K∪d. Every connected component of this open plane set is open by the same
connected-ball argument, so the argument uses no unproved path/component regularity assertion.

M2. Collect the connector's finitely many segments in a finite set S, retaining a walk
through their endpoint pairs. Their union Q is compact and avoids M. A positive closed-ball
collar about M therefore misses Q. Write M=l(t) in the injective affine parametrization of
the original stub. Choose ε>0 so that t±ε/2 lie in (0,1) and their images lie in the collar.
The images v,w are distinct and M is interior to [v,w]. Convexity puts [v,w] in the original
stub and collar, so this central segment misses Q and K, meets d exactly at M, and lies on
the original stub line.

M3. Set X=Q∪[x_-,v]∪[w,x_+]. Injectivity of l and the ordered parameter intervals prove
X∩[v,w]⊆{v,w}. Thus X misses K and d. Traversing the first stub tail, the original connector,
and the other tail gives a finite segment chain from v to w in X. On all plane points, form
the simple graph whose edges are the distinct pairs with entire closed segment in X. The
chain gives graph reachability after omitting stationary steps. Mathlib supplies a shortest
path q from v to w, with length equal to graph distance and without repeated vertices.
For any walk r from vertex q_i to q_j, retaining q's prefix through i and suffix from j gives
another endpoint walk. Minimality implies j≤i+length(r). This uses only natural-number
lengths and does not require the graph to have finitely many vertices.

M4. Suppose nonadjacent connector edges i and j, with i+1<j, meet at z. Their subsegments
q_i--z and z--q_(j+1) lie in X and give a walk of length at most two; the preceding bound
implies j+1≤i+2, a contradiction. If adjacent edges i,i+1 meet away from their common
vertex, their three endpoints are collinear: both segments lie on the line through the
common vertex and that second intersection. The segment joining the outer endpoints lies
in the union of the two old segments (split its open segment at the middle point on the
same affine line). It therefore gives a walk of length at most one, contradicting
(i+2)≤i+1. Thus adjacent connector edges meet only at the common endpoint. Also, if q_k
lies on edge i, its two subsegments give k≤i+1 and i≤k, so k=i or k=i+1. This controls any
connector edge that meets v or w.

M5. The shortest connector has at least two edges: a direct edge v--w would put M in X,
contrary to X missing d. If its length is n+2, take its n+3 vertices as a native Polygon,
closing with w--v. Its vertices are injective and its cyclic edges are nondegenerate.
M4 gives the exact intersections for pairs of connector edges. A connector edge meets
the closing edge only at v or w by M3, and M4's vertex-on-edge argument ensures that these
are common endpoints of the two edges. The reverse inclusion follows because endpoints
belong to their edges. The connector lies in X and the closing edge in the original stub,
so the boundary misses K and meets d exactly at M. The closing edge contains M strictly
inside and lies on the original stub line. This proves the exact stated marked polygon.

The complete Lean proof follows this shortest-path argument. All geometric shortcut and
endpoint arguments are local steps of this existing agent-origin omission expansion; no
additional agent-origin helper is assumed. The original nonparallel hypothesis is retained
in the public statement and ensures transversality of the retained stub-line edge.
-/
theorem cairns_marked_segment_polygon_closure
    (K : Set ℂ) (hK : IsCompact K)
    (D₁ D₂ M xminus xplus : ℂ)
    (_hd_nondegenerate : D₁ ≠ D₂)
    (hM_d : M ∈ openSegment ℝ D₁ D₂)
    (hs_nondegenerate : xminus ≠ xplus)
    (hs_K : Disjoint (segment ℝ xminus xplus) K)
    (hs_d : segment ℝ xminus xplus ∩ segment ℝ D₁ D₂ = {M})
    (hM_s : M ∈ openSegment ℝ xminus xplus)
    (_h_nonparallel : ¬ ∃ t : ℝ, xplus - xminus = t • (D₂ - D₁))
    (h_component : xplus ∈ connectedComponentIn (K ∪ segment ℝ D₁ D₂)ᶜ xminus) :
    ∃ (n : ℕ) (p : Polygon ℂ (n + 3)),
      Function.Injective p.vertices ∧
      p.HasNondegenerateEdges ∧
      (∀ (i j : Fin (n + 3)), i ≠ j →
        p.edgeSet ℝ i ∩ p.edgeSet ℝ j =
          ({p i, p (finRotate (n + 3) i)} : Set ℂ) ∩
          {p j, p (finRotate (n + 3) j)}) ∧
      Disjoint (p.boundary ℝ) K ∧
      p.boundary ℝ ∩ segment ℝ D₁ D₂ = {M} ∧
      ∃ i : Fin (n + 3),
        M ∈ openSegment ℝ (p i) (p (finRotate (n + 3) i)) ∧
        p.edgeSet ℝ i ⊆ (line[ℝ, xminus, xplus] : Set ℂ) := by
  have hdcompact : IsCompact (segment ℝ D₁ D₂) := by
    rw [← convexHull_pair]
    exact ((Set.finite_singleton D₂).insert D₁).isCompact_convexHull ℝ
  have hopen : IsOpen (K ∪ segment ℝ D₁ D₂)ᶜ :=
    (hK.isClosed.union hdcompact.isClosed).isOpen_compl
  have hminus : xminus ∈ (K ∪ segment ℝ D₁ D₂)ᶜ :=
    connectedComponentIn_nonempty_iff.mp ⟨xplus, h_component⟩
  have hconnector := open_preconnected_segment_chain hopen.connectedComponentIn
    isPreconnected_connectedComponentIn (mem_connectedComponentIn hminus) h_component
  have hfinite : ∃ S : Finset (ℂ × ℂ),
      Relation.ReflTransGen (fun p q ↦ (p, q) ∈ S) xminus xplus ∧
      xminus ∈ ⋃ q ∈ S, segment ℝ q.1 q.2 ∧
      xplus ∈ ⋃ q ∈ S, segment ℝ q.1 q.2 ∧
      (⋃ q ∈ S, segment ℝ q.1 q.2) ⊆ (K ∪ segment ℝ D₁ D₂)ᶜ := by
    classical
    clear hs_nondegenerate hs_K hs_d hM_s _h_nonparallel h_component
    induction hconnector with
    | refl =>
      refine ⟨{(xminus, xminus)}, .refl, ?_, ?_, ?_⟩
      · simp
      · simp
      · simpa using singleton_subset_iff.mpr hminus
    | @tail b c hprev hbc ih =>
      obtain ⟨S, hwalk, ha, hb, hS⟩ := ih
      refine ⟨insert (b, c) S, ?_, ?_, ?_, ?_⟩
      · exact (Relation.ReflTransGen.mono (fun _ _ h ↦ Finset.mem_insert_of_mem h) _ _ hwalk).tail
          (Finset.mem_insert_self _ _)
      · simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left]
        exact Or.inr ha
      · simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left]
        exact Or.inl (right_mem_segment ℝ b c)
      · intro z hz
        simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left, mem_union] at hz
        exact hz.elim (fun hz ↦ connectedComponentIn_subset _ _ (hbc hz)) (fun hz ↦ hS hz)
  obtain ⟨S, hSwalk, hSminus, hSplus, hSavoid⟩ := hfinite
  have hScompact : IsCompact (⋃ q ∈ S, segment ℝ q.1 q.2) := by
    apply S.finite_toSet.isCompact_biUnion
    intro q _
    rw [← convexHull_pair]
    exact ((Set.finite_singleton q.2).insert q.1).isCompact_convexHull ℝ
  have hMavoid : M ∉ ⋃ q ∈ S, segment ℝ q.1 q.2 := by
    intro hM
    exact hSavoid hM (Or.inr (openSegment_subset_segment ℝ D₁ D₂ hM_d))
  have hnear : ∃ δ : ℝ, 0 < δ ∧
      Metric.closedBall M δ ⊆ (⋃ q ∈ S, segment ℝ q.1 q.2)ᶜ :=
    Metric.nhds_basis_closedBall.mem_iff.mp (hScompact.isClosed.isOpen_compl.mem_nhds hMavoid)
  obtain ⟨δ, hδ, hδavoid⟩ := hnear
  obtain ⟨t, ht, hMt⟩ := (openSegment_eq_image_lineMap ℝ xminus xplus ▸ hM_s)
  let l := AffineMap.lineMap xminus xplus (k := ℝ)
  have hl : Continuous l := by fun_prop
  have hT : IsOpen (Ioo (0 : ℝ) 1 ∩ l ⁻¹' Metric.ball M δ) :=
    isOpen_Ioo.inter (Metric.isOpen_ball.preimage hl)
  have htT : t ∈ Ioo (0 : ℝ) 1 ∩ l ⁻¹' Metric.ball M δ := by
    exact ⟨ht, hMt.symm ▸ Metric.mem_ball_self hδ⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hT t htT
  have hleft : t - ε / 2 ∈ Metric.ball t ε := by
    rw [Metric.mem_ball, Real.dist_eq,
      show t - ε / 2 - t = -(ε / 2) by ring, abs_neg, abs_of_pos (half_pos hε)]
    linarith
  have hright : t + ε / 2 ∈ Metric.ball t ε := by
    rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left,
      abs_of_pos (half_pos hε)]
    linarith
  let v := l (t - ε / 2)
  let w := l (t + ε / 2)
  have hvw : v ≠ w := by
    intro hvw
    have := (AffineMap.lineMap_eq_lineMap_iff.mp hvw).resolve_left hs_nondegenerate
    linarith
  have hcentral : M ∈ openSegment ℝ v w := by
    rw [← hMt, ← image_openSegment]
    refine ⟨t, Ioo_subset_openSegment ⟨?_, ?_⟩, rfl⟩ <;> linarith
  have hcentral_sub : segment ℝ v w ⊆ segment ℝ xminus xplus ∩ Metric.closedBall M δ := by
    apply (convex_segment xminus xplus).inter (convex_closedBall M δ) |>.segment_subset
    · exact ⟨openSegment_subset_segment ℝ _ _
        (lineMap_mem_openSegment ℝ _ _ (hεsub hleft).1),
        Metric.ball_subset_closedBall (hεsub hleft).2⟩
    · exact ⟨openSegment_subset_segment ℝ _ _
        (lineMap_mem_openSegment ℝ _ _ (hεsub hright).1),
        Metric.ball_subset_closedBall (hεsub hright).2⟩
  have hcentral_avoid : Disjoint (segment ℝ v w) (⋃ q ∈ S, segment ℝ q.1 q.2) :=
    Set.disjoint_left.mpr (fun _ hz hq ↦ hδavoid (hcentral_sub hz).2 hq)
  have hcentral_K : Disjoint (segment ℝ v w) K :=
    hs_K.mono_left (fun _ hz ↦ (hcentral_sub hz).1)
  have hcentral_d : segment ℝ v w ∩ segment ℝ D₁ D₂ = {M} := by
    apply subset_antisymm
    · exact (inter_subset_inter_left _ (fun _ hz ↦ (hcentral_sub hz).1)).trans hs_d.subset
    · rintro z (rfl : z = M)
      exact ⟨openSegment_subset_segment ℝ v w hcentral,
        openSegment_subset_segment ℝ D₁ D₂ hM_d⟩
  have hcentral_line : segment ℝ v w ⊆ (line[ℝ, xminus, xplus] : Set ℂ) := by
    calc
      segment ℝ v w ⊆ segment ℝ xminus xplus := fun _ hz ↦ (hcentral_sub hz).1
      _ ⊆ (line[ℝ, xminus, xplus] : Set ℂ) := by
        simpa only [affineSegment_eq_segment] using
          affineSegment_subset_affineSpan ℝ xminus xplus
  let X := (⋃ q ∈ S, segment ℝ q.1 q.2) ∪ segment ℝ xminus v ∪ segment ℝ w xplus
  have hlinj : Function.Injective l := AffineMap.lineMap_injective ℝ hs_nondegenerate
  have hvparam := (hεsub hleft).1
  have hwparam := (hεsub hright).1
  have hXcentral : ∀ z ∈ X, z ∈ segment ℝ v w → z = v ∨ z = w := by
    intro z hz hzvw
    have hparams : segment ℝ v w = l '' Icc (t - ε / 2) (t + ε / 2) := by
      rw [← segment_eq_Icc (show t - ε / 2 ≤ t + ε / 2 by linarith), image_segment]
    rw [hparams] at hzvw
    obtain ⟨r, hr, rfl⟩ := hzvw
    rcases hz with (hz | hz) | hz
    · exact (Set.disjoint_left.mp hcentral_avoid
        (hparams.symm ▸ ⟨r, hr, rfl⟩) hz).elim
    · have hparams0 : segment ℝ xminus v = l '' Icc 0 (t - ε / 2) := by
        rw [← segment_eq_Icc hvparam.1.le, image_segment]
        simp only [l, AffineMap.lineMap_apply_zero, v]
      rw [hparams0] at hz
      obtain ⟨r', hr', heq⟩ := hz
      have heq' := hlinj heq
      left
      have : r = t - ε / 2 := by linarith [hr.1, hr'.2]
      exact congrArg l this
    · have hparams1 : segment ℝ w xplus = l '' Icc (t + ε / 2) 1 := by
        rw [← segment_eq_Icc hwparam.2.le, image_segment]
        simp only [l, AffineMap.lineMap_apply_one, w]
      rw [hparams1] at hz
      obtain ⟨r', hr', heq⟩ := hz
      have heq' := hlinj heq
      right
      have : r = t + ε / 2 := by linarith [hr.2, hr'.1]
      exact congrArg l this
  have hvstub : v ∈ segment ℝ xminus xplus :=
    (hcentral_sub (left_mem_segment ℝ v w)).1
  have hwstub : w ∈ segment ℝ xminus xplus :=
    (hcentral_sub (right_mem_segment ℝ v w)).1
  have hXK : Disjoint X K := by
    apply Set.disjoint_left.mpr
    intro z hz hzK
    rcases hz with (hz | hz) | hz
    · exact hSavoid hz (Or.inl hzK)
    · exact Set.disjoint_left.mp hs_K ((convex_segment xminus xplus).segment_subset
        (left_mem_segment ℝ _ _) hvstub hz) hzK
    · exact Set.disjoint_left.mp hs_K ((convex_segment xminus xplus).segment_subset
        hwstub (right_mem_segment ℝ _ _) hz) hzK
  have hXd : Disjoint X (segment ℝ D₁ D₂) := by
    apply Set.disjoint_left.mpr
    intro z hz hzd
    have hzM : z = M := by
      rcases hz with (hz | hz) | hz
      · exact (hSavoid hz (Or.inr hzd)).elim
      · exact hs_d.subset ⟨(convex_segment xminus xplus).segment_subset
          (left_mem_segment ℝ _ _) hvstub hz, hzd⟩
      · exact hs_d.subset ⟨(convex_segment xminus xplus).segment_subset
          hwstub (right_mem_segment ℝ _ _) hz, hzd⟩
    subst z
    rcases hXcentral M hz (openSegment_subset_segment ℝ _ _ hcentral) with h | h
    · have := hlinj (hMt.trans h)
      linarith
    · have := hlinj (hMt.trans h)
      linarith
  have hXchain : Relation.ReflTransGen (fun a b ↦ segment ℝ a b ⊆ X) v w := by
    have hmid : Relation.ReflTransGen (fun a b ↦ segment ℝ a b ⊆ X) xminus xplus :=
      Relation.ReflTransGen.mono (fun a b hab ↦ by
        intro z hz
        exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨(a, b), Set.mem_iUnion.mpr ⟨hab, hz⟩⟩)))
        _ _ hSwalk
    have hfirst : Relation.ReflTransGen (fun a b ↦ segment ℝ a b ⊆ X) v xminus :=
      .single (by intro z hz; exact Or.inl (Or.inr (segment_symm ℝ v xminus ▸ hz)))
    have hlast : Relation.ReflTransGen (fun a b ↦ segment ℝ a b ⊆ X) xplus w :=
      .single (by intro z hz; exact Or.inr (segment_symm ℝ xplus w ▸ hz))
    exact hfirst.trans (hmid.trans hlast)
  obtain ⟨n, p, hpinj, hpnondeg, hinter, hpzero, hplast, hothers, _⟩ :=
    segment_chain_polygon_closure X v w hvw hXcentral
      (fun h ↦ Set.disjoint_left.mp hXd (h (openSegment_subset_segment ℝ _ _ hcentral))
        (openSegment_subset_segment ℝ _ _ hM_d)) hXchain
  have hlastedge : p.edgeSet ℝ (Fin.last (n + 2)) = segment ℝ w v := by
    simp only [Polygon.edgeSet, finRotate_last, hplast, hpzero, affineSegment_eq_segment]
  refine ⟨n, p, hpinj, hpnondeg, hinter, ?_, ?_, Fin.last (n + 2), ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro z hz hzK
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    by_cases hidx : i = Fin.last (n + 2)
    · subst i
      rw [hlastedge, segment_symm] at hi
      exact Set.disjoint_left.mp hcentral_K hi hzK
    · exact Set.disjoint_left.mp hXK (hothers i hidx hi) hzK
  · apply subset_antisymm
    · rintro z ⟨hz, hzd⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      by_cases hidx : i = Fin.last (n + 2)
      · subst i
        rw [hlastedge, segment_symm] at hi
        exact hcentral_d.subset ⟨hi, hzd⟩
      · exact (Set.disjoint_left.mp hXd (hothers i hidx hi) hzd).elim
    · rintro z (rfl : z = M)
      exact ⟨Set.mem_iUnion.mpr ⟨Fin.last (n + 2), by
        rw [hlastedge, segment_symm]
        exact openSegment_subset_segment ℝ _ _ hcentral⟩,
        openSegment_subset_segment ℝ _ _ hM_d⟩
  · simpa only [finRotate_last, hplast, hpzero, openSegment_symm] using hcentral
  · rw [hlastedge, segment_symm]
    exact hcentral_line

end HolomorphicAnosov
