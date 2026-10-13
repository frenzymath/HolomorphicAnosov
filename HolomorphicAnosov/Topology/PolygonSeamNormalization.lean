import HolomorphicAnosov.Topology.PolygonInsertVertex
import HolomorphicAnosov.Topology.PolygonDeleteVertexSimplicity
import HolomorphicAnosov.Topology.CollinearSegmentsJoint
import HolomorphicAnosov.Topology.PolygonEdgeCompact
import Mathlib.Analysis.Convex.Topology

/-!
# A straight boundary seam as one polygon edge

Source context: Cairns (1951), preliminary §2(B) and Theorem 2.1, pp.860–861.
The explicit finite normalization proof is agent-written.
DAG node: `topo.polygon_standard_seam_g17`.

Insert both seam endpoints into the vertex list. At a vertex in the open seam,
remove the finite closed union of all nonincident edges from a small neighborhood.
Small homothetic copies of the seam endpoints lie in that neighborhood, with the
vertex strictly between them. They lie on the two incident edges. They cannot both
lie on one edge, since an endpoint of a segment is never strictly between two of
its points. Thus the incident edges are collinear. Simplicity excludes reversal,
so the existing redundant-vertex lemmas delete the vertex while preserving the
boundary, simplicity, and both seam endpoints. Induction terminates because the
vertex count decreases and remains at least three.

Now the open seam contains no vertex. Its connectedness and the finite closed edge
cover imply that it lies in one edge: otherwise that edge and the union of the
others give a closed separation, whose intersection would contain a vertex in the
open seam. Taking closures puts the closed seam in that edge. Since both seam
endpoints are listed vertices, the vertex-on-edge property identifies them as the
edge's two endpoints. Rotate or reverse the cyclic list to place a first and b last.
-/

namespace HolomorphicAnosov
open Set

lemma endpoint_not_strict_between {u x y z : ℂ}
    (hy : y ∈ segment ℝ x u) (hz : z ∈ segment ℝ x u)
    (h : Sbtw ℝ y x z) : False := by
  have hy' := mem_segment_iff_wbtw.mp hy
  have hz' := mem_segment_iff_wbtw.mp hz
  have hzx : Wbtw ℝ z x u := h.symm.wbtw.trans_expand_left hy' h.ne_left
  exact h.ne_right (hz'.swap_left_iff.mp hzx)

lemma incident_segments_collinear {u x v y z : ℂ}
    (hy : y ∈ segment ℝ u x ∪ segment ℝ x v)
    (hz : z ∈ segment ℝ u x ∪ segment ℝ x v)
    (hs : Sbtw ℝ y x z) : Collinear ℝ ({u, x, v} : Set ℂ) := by
  have cross {y z : ℂ} (hy : y ∈ segment ℝ u x) (hz : z ∈ segment ℝ x v)
      (hs : Sbtw ℝ y x z) : Collinear ℝ ({u, x, v} : Set ℂ) := by
    have hu : u ∈ line[ℝ, y, x] :=
      (mem_segment_iff_wbtw.mp hy).collinear.mem_affineSpan_of_mem_of_ne
        (by simp) (by simp) (by simp) hs.left_ne
    have hv : v ∈ line[ℝ, x, z] :=
      (mem_segment_iff_wbtw.mp hz).collinear.mem_affineSpan_of_mem_of_ne
        (by simp) (by simp) (by simp) hs.ne_right
    have heq : line[ℝ, x, z] = line[ℝ, y, x] :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne
        (right_mem_affineSpan_pair ℝ y x)
        (hs.wbtw.collinear.mem_affineSpan_of_mem_of_ne
          (by simp) (by simp) (by simp) hs.left_ne) hs.ne_right
    rw [heq] at hv
    exact collinear_triple_of_mem_affineSpan_pair hu (right_mem_affineSpan_pair ℝ y x) hv
  rcases hy with hy | hy <;> rcases hz with hz | hz
  · exact (endpoint_not_strict_between (segment_symm ℝ u x ▸ hy)
      (segment_symm ℝ u x ▸ hz) hs).elim
  · exact cross hy hz hs
  · exact cross hz hy hs.symm
  · exact (endpoint_not_strict_between hy hz hs).elim

lemma small_subsegment_through {a b x : ℂ} (hab : a ≠ b)
    (hx : x ∈ openSegment ℝ a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ y z : ℂ, y ∈ segment ℝ a b ∧ z ∈ segment ℝ a b ∧
      y ∈ Metric.ball x ε ∧ z ∈ Metric.ball x ε ∧ Sbtw ℝ y x z := by
  have hxnleft : x ≠ a := by
    rintro rfl
    exact hab (left_mem_openSegment_iff.mp hx)
  have hxnright : x ≠ b := by
    rintro rfl
    exact hab (right_mem_openSegment_iff.mp hx)
  have hsb : Sbtw ℝ a x b :=
    ⟨mem_segment_iff_wbtw.mp (openSegment_subset_segment ℝ a b hx), hxnleft, hxnright⟩
  have hca : ContinuousAt (fun t : ℝ ↦ AffineMap.homothety x t a) 0 := by
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
    fun_prop
  have hcb : ContinuousAt (fun t : ℝ ↦ AffineMap.homothety x t b) 0 := by
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
    fun_prop
  obtain ⟨δa, hδa, ha⟩ := Metric.continuousAt_iff.mp hca ε hε
  obtain ⟨δb, hδb, hb⟩ := Metric.continuousAt_iff.mp hcb ε hε
  let t := min 1 (min δa δb) / 2
  have ht : 0 < t := half_pos (lt_min zero_lt_one (lt_min hδa hδb))
  have htmin : t < min 1 (min δa δb) := half_lt_self (lt_min zero_lt_one (lt_min hδa hδb))
  have ht1 : t ≤ 1 := htmin.le.trans (min_le_left _ _)
  have hta : t < δa := htmin.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htb : t < δb := htmin.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hxseg := openSegment_subset_segment ℝ a b hx
  refine ⟨AffineMap.homothety x t a, AffineMap.homothety x t b, ?_, ?_, ?_, ?_, ?_⟩
  · rw [AffineMap.homothety_eq_lineMap]
    exact (convex_segment a b).segment_subset hxseg (left_mem_segment ℝ a b)
      (by rw [segment_eq_image_lineMap]; exact ⟨t, ⟨ht.le, ht1⟩, rfl⟩)
  · rw [AffineMap.homothety_eq_lineMap]
    exact (convex_segment a b).segment_subset hxseg (right_mem_segment ℝ a b)
      (by rw [segment_eq_image_lineMap]; exact ⟨t, ⟨ht.le, ht1⟩, rfl⟩)
  · have := ha (x := t) (by simpa only [Real.dist_eq, sub_zero, abs_of_pos ht] using hta)
    simpa using this
  · have := hb (x := t) (by simpa only [Real.dist_eq, sub_zero, abs_of_pos ht] using htb)
    simpa using this
  · simpa only [AffineMap.homothety_apply_same] using
      (AffineMap.homothety_injective x ht.ne').sbtw_map_iff.mpr hsb

lemma PolygonCycleData.collinear_of_vertex_in_segment {n : ℕ} {p : Polygon ℂ (n + 3)}
    (h : PolygonCycleData p) (a b : ℂ) (hab : a ≠ b)
    (hsub : segment ℝ a b ⊆ p.boundary ℝ)
    (i : Fin (n + 3)) (hi : p i ∈ openSegment ℝ a b) :
    Collinear ℝ ({p ((finRotate (n + 3)).symm i), p i,
      p (finRotate (n + 3) i)} : Set ℂ) := by
  classical
  let F : Set ℂ := ⋃ j : {j : Fin (n + 3) // j ≠ i ∧ finRotate (n + 3) j ≠ i},
    p.edgeSet ℝ j.val
  have hFclosed : IsClosed F := by
    apply isClosed_iUnion_of_finite
    intro j
    rw [Polygon.edgeSet, affineSegment_eq_segment]
    rw [← convexHull_pair]
    exact ((Set.finite_singleton (p (finRotate (n + 3) j.val))).insert (p j.val)).isCompact_convexHull ℝ |>.isClosed
  have hiF : p i ∉ F := by
    intro hm
    obtain ⟨j, hj⟩ := mem_iUnion.mp hm
    rcases (h.vertex_mem_edge i j).mp hj with he | he
    · exact j.property.1 he.symm
    · exact j.property.2 he.symm
  obtain ⟨ε, hε, he⟩ := Metric.mem_nhds_iff.mp (hFclosed.isOpen_compl.mem_nhds hiF)
  have hlocal {z : ℂ} (hz : z ∈ segment ℝ a b) (hzball : z ∈ Metric.ball (p i) ε) :
      z ∈ segment ℝ (p ((finRotate (n + 3)).symm i)) (p i) ∪
        segment ℝ (p i) (p (finRotate (n + 3) i)) := by
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hsub hz)
    by_cases hji : j = i
    · subst j
      exact Or.inr (by simpa only [Polygon.edgeSet, affineSegment_eq_segment] using hj)
    have hrot : finRotate (n + 3) j = i := by
      by_contra hr
      exact he hzball (mem_iUnion.mpr ⟨⟨j, hji, hr⟩, hj⟩)
    have hjprev : j = (finRotate (n + 3)).symm i := by
      exact (Equiv.eq_symm_apply _).mpr hrot
    subst j
    exact Or.inl (by simpa only [Polygon.edgeSet, affineSegment_eq_segment,
      Equiv.apply_symm_apply] using hj)
  obtain ⟨y, z, hy, hz, hyball, hzball, hsb⟩ := small_subsegment_through hab hi hε
  exact incident_segments_collinear (hlocal hy hyball) (hlocal hz hzball) hsb


lemma PolygonCycleData.delete_collinear {n : ℕ} {p : Polygon ℂ (n + 3)}
    (h : PolygonCycleData p) (i : Fin (n + 3))
    (hc : Collinear ℝ ({p ((finRotate (n + 3)).symm i), p i,
      p (finRotate (n + 3) i)} : Set ℂ)) :
    let q : Polygon ℂ (n + 2) := ⟨fun j ↦ p (i.succAbove j)⟩
    3 ≤ n + 2 ∧ PolygonCycleData q ∧ q.boundary ℝ = p.boundary ℝ ∧
      range q.vertices = range p.vertices \ {p i} := by
  intro q
  have hrot (j : Fin (n + 3)) : finRotate (n + 3) j ≠ j := by
    intro he
    exact h.nondegenerate j (congrArg p he.symm)
  have hrot2 : finRotate (n + 3) (finRotate (n + 3) i) ≠ i := by
    intro he
    have hv := congrArg Fin.val he
    have h₁ := coe_finRotate i
    have h₂ := coe_finRotate (finRotate (n + 3) i)
    simp only [Fin.ext_iff, Fin.val_last] at h₁ h₂
    change (finRotate (n + 3) i).val =
      (if i.val = n + 2 then 0 else i.val + 1) at h₁
    change (finRotate (n + 3) (finRotate (n + 3) i)).val =
      (if (finRotate (n + 3) i).val = n + 2 then 0
        else (finRotate (n + 3) i).val + 1) at h₂
    split_ifs at h₁ h₂ <;> omega
  have hprev : (finRotate (n + 3)).symm i ≠ i := by
    intro he
    exact hrot i (by simpa using congrArg (finRotate (n + 3)) he.symm)
  have hpn : (finRotate (n + 3)).symm i ≠ finRotate (n + 3) i := by
    intro he
    exact hrot2 (by simpa using (congrArg (finRotate (n + 3)) he).symm)
  have hi := collinear_segments_meeting_only_at_joint
    (p ((finRotate (n + 3)).symm i)) (p i) (p (finRotate (n + 3) i))
    (h.injective.ne hprev) (h.nondegenerate i) hc (by
      intro z hz
      have hh := h.simple ((finRotate (n + 3)).symm i) i hprev
      simp only [Polygon.edgeSet, affineSegment_eq_segment, Equiv.apply_symm_apply] at hh
      have he := hh hz
      rcases he.1 with he₁ | he₁
      · rcases he.2 with he' | he'
        · exact (h.injective.ne hprev (he₁.symm.trans he')).elim
        · exact (h.injective.ne hpn (he₁.symm.trans he')).elim
      · exact he₁)
  have hd := polygon_delete_vertex_simplicity p i (by omega) h.injective h.indexed_simple hi.1 hi.2
  refine ⟨hd.1, PolygonCycleData.of_indexed hd.2.1 hd.2.2.2,
    polygon_boundary_delete_vertex (by omega) p i hi.2, ?_⟩
  ext z
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨⟨i.succAbove j, rfl⟩, ?_⟩
    intro he
    exact Fin.succAbove_ne i j (h.injective he)
  · rintro ⟨⟨j, rfl⟩, hj⟩
    have hji : j ≠ i := by rintro rfl; exact hj rfl
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
    exact ⟨k, rfl⟩

lemma PolygonCycleData.add_boundary_vertex {n : ℕ} {p : Polygon ℂ (n + 3)}
    (h : PolygonCycleData p) (x : ℂ) (hx : x ∈ p.boundary ℝ) :
    ∃ m : ℕ, ∃ q : Polygon ℂ (m + 3), PolygonCycleData q ∧
      q.boundary ℝ = p.boundary ℝ ∧ range p.vertices ⊆ range q.vertices ∧
      x ∈ range q.vertices := by
  classical
  by_cases hv : x ∈ range p.vertices
  · exact ⟨n, p, h, rfl, subset_rfl, hv⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  have hxleft : p i ≠ x := fun he ↦ hv ⟨i, he⟩
  have hxright : p (finRotate (n + 3) i) ≠ x := fun he ↦ hv ⟨finRotate (n + 3) i, he⟩
  have hxopen : x ∈ openSegment ℝ (p i) (p (finRotate (n + 3) i)) :=
    mem_openSegment_of_ne_left_right hxleft hxright
      (by simpa only [Polygon.edgeSet, affineSegment_eq_segment] using hi)
  exact ⟨n + 1, _, h.insert_vertex i x hxopen⟩

lemma PolygonCycleData.normalize_seam {n : ℕ} {p : Polygon ℂ (n + 3)}
    (h : PolygonCycleData p) (a b : ℂ) (hab : a ≠ b)
    (hsub : segment ℝ a b ⊆ p.boundary ℝ)
    (ha : a ∈ range p.vertices) (hb : b ∈ range p.vertices) :
    ∃ m : ℕ, ∃ q : Polygon ℂ (m + 3), PolygonCycleData q ∧
      q.boundary ℝ = p.boundary ℝ ∧ a ∈ range q.vertices ∧ b ∈ range q.vertices ∧
      ∀ i, q i ∉ openSegment ℝ a b := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    classical
    by_cases hall : ∀ i, p i ∉ openSegment ℝ a b
    · exact ⟨n, p, h, rfl, ha, hb, hall⟩
    push Not at hall
    obtain ⟨i, hi⟩ := hall
    have hc := h.collinear_of_vertex_in_segment a b hab hsub i hi
    have hd := h.delete_collinear i hc
    have hn : 0 < n := by have := hd.1; omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    let q : Polygon ℂ (k + 3) := ⟨fun j ↦ p (i.succAbove j)⟩
    have hqa : a ∈ range q.vertices := by
      rw [hd.2.2.2]
      refine ⟨ha, ?_⟩
      intro he
      exact hab (left_mem_openSegment_iff.mp (he.symm ▸ hi))
    have hqb : b ∈ range q.vertices := by
      rw [hd.2.2.2]
      refine ⟨hb, ?_⟩
      intro he
      exact hab (right_mem_openSegment_iff.mp (he.symm ▸ hi))
    obtain ⟨m, r, hr, hrb, hra, hrbb, hrnone⟩ :=
      ih k (by omega) hd.2.1 (by simpa only [hd.2.2.1] using hsub) hqa hqb
    exact ⟨m, r, hr, hrb.trans hd.2.2.1, hra, hrbb, hrnone⟩


lemma PolygonCycleData.seam_is_edge {n : ℕ} {p : Polygon ℂ (n + 3)}
    (h : PolygonCycleData p) (a b : ℂ) (hab : a ≠ b)
    (hsub : segment ℝ a b ⊆ p.boundary ℝ)
    (ha : a ∈ range p.vertices) (hb : b ∈ range p.vertices)
    (hnone : ∀ i, p i ∉ openSegment ℝ a b) :
    ∃ j, (p j = a ∧ p (finRotate (n + 3) j) = b) ∨
      (p j = b ∧ p (finRotate (n + 3) j) = a) := by
  classical
  have hm : midpoint ℝ a b ∈ openSegment ℝ a b := midpoint_mem_openSegment a b
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hsub (openSegment_subset_segment ℝ a b hm))
  let F : Set ℂ := ⋃ i : {i : Fin (n + 3) // i ≠ j}, p.edgeSet ℝ i.val
  have hFclosed : IsClosed F := isClosed_iUnion_of_finite fun i ↦ (p.isCompact_edgeSet i).isClosed
  have hsedge : openSegment ℝ a b ⊆ p.edgeSet ℝ j := by
    intro y hy
    by_contra hyj
    have hsF : y ∈ F := by
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hsub (openSegment_subset_segment ℝ a b hy))
      exact mem_iUnion.mpr ⟨⟨i, fun he ↦ hyj (he ▸ hi)⟩, hi⟩
    have hcover : openSegment ℝ a b ⊆ p.edgeSet ℝ j ∪ F := by
      intro z hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hsub (openSegment_subset_segment ℝ a b hz))
      by_cases hij : i = j
      · exact Or.inl (hij ▸ hi)
      · exact Or.inr (mem_iUnion.mpr ⟨⟨i, hij⟩, hi⟩)
    obtain ⟨z, hz, hzj, hzF⟩ := isPreconnected_closed_iff.mp
      (convex_openSegment a b).isPreconnected (p.edgeSet ℝ j) F
      (p.isCompact_edgeSet j).isClosed hFclosed hcover ⟨_, hm, hj⟩ ⟨y, hy, hsF⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hzF
    have he := (h.simple j i (Ne.symm i.property) ⟨hzj, hi⟩).1
    rcases he with he | he
    · exact hnone j (he ▸ hz)
    · exact hnone (finRotate (n + 3) j) (he ▸ hz)
  have hseg : segment ℝ a b ⊆ p.edgeSet ℝ j := by
    rw [← closure_openSegment a b]
    exact closure_minimal hsedge (p.isCompact_edgeSet j).isClosed
  obtain ⟨ia, hia⟩ := ha
  obtain ⟨ib, hib⟩ := hb
  have haedge : p ia ∈ p.edgeSet ℝ j := hia ▸ hseg (left_mem_segment ℝ a b)
  have hbedge : p ib ∈ p.edgeSet ℝ j := hib ▸ hseg (right_mem_segment ℝ a b)
  refine ⟨j, ?_⟩
  rcases (h.vertex_mem_edge ia j).mp haedge with haj | haj <;>
    rcases (h.vertex_mem_edge ib j).mp hbedge with hbj | hbj <;>
      simp only [haj, hbj] at hia hib
  · exact (hab (hia.symm.trans hib)).elim
  · exact Or.inl ⟨hia, hib⟩
  · exact Or.inr ⟨hib, hia⟩
  · exact (hab (hia.symm.trans hib)).elim


lemma PolygonCycleData.orient_seam {n : ℕ} {p : Polygon ℂ (n + 3)}
    (h : PolygonCycleData p) (a b : ℂ)
    (hj : ∃ j, (p j = a ∧ p (finRotate (n + 3) j) = b) ∨
      (p j = b ∧ p (finRotate (n + 3) j) = a)) :
    ∃ q : Polygon ℂ (n + 3), PolygonCycleData q ∧ q.boundary ℝ = p.boundary ℝ ∧
      q 0 = a ∧ q (Fin.last (n + 2)) = b := by
  obtain ⟨j, hj⟩ := hj
  rcases hj with ⟨hja, hjb⟩ | ⟨hjb, hja⟩
  · let e : Equiv.Perm (Fin (n + 3)) :=
      ⟨fun i ↦ j - i, fun i ↦ j - i, by intro i; simp, by intro i; simp⟩
    let f := e.trans (finRotate (n + 3)).symm
    have he (i : Fin (n + 3)) : e (finRotate (n + 3) i) = f i := by
      simp only [e, f, Equiv.coe_trans, Function.comp_apply, finRotate_symm_apply,
        finRotate_apply, Equiv.coe_fn_mk]
      abel
    have hr := h.reindex e f (fun i ↦ Or.inr ⟨by simp [f], he i⟩)
    refine ⟨_, hr.1, hr.2, ?_, ?_⟩
    · simpa [e] using hja
    · simpa [e, sub_eq_add_neg, ← finRotate_apply] using hjb
  · let e := Equiv.addLeft (finRotate (n + 3) j)
    have he (i : Fin (n + 3)) : e (finRotate (n + 3) i) = finRotate (n + 3) (e i) := by
      simp [e, finRotate_apply, add_assoc]
    have hr := h.reindex e e (fun i ↦ Or.inl ⟨rfl, he i⟩)
    refine ⟨_, hr.1, hr.2, ?_, ?_⟩
    · simpa [e] using hja
    · have hlast : (Fin.last (n + 2) : Fin (n + 3)) = -1 := by
        exact neg_eq_iff_eq_neg.mp (Fin.neg_last (n + 2))
      simpa [e, finRotate_apply, hlast, add_assoc] using hjb

lemma PolygonCycleData.standard_seam {n : ℕ} {p : Polygon ℂ (n + 3)}
    (h : PolygonCycleData p) (a b : ℂ) (hab : a ≠ b)
    (hsub : segment ℝ a b ⊆ p.boundary ℝ) :
    ∃ m : ℕ, ∃ q : Polygon ℂ (m + 3), PolygonCycleData q ∧
      q.boundary ℝ = p.boundary ℝ ∧ q 0 = a ∧ q (Fin.last (m + 2)) = b := by
  obtain ⟨m₁, q₁, hq₁, hb₁, hverts₁, ha⟩ :=
    h.add_boundary_vertex a (hsub (left_mem_segment ℝ a b))
  obtain ⟨m₂, q₂, hq₂, hb₂, hverts₂, hb⟩ :=
    hq₁.add_boundary_vertex b (by rw [hb₁]; exact hsub (right_mem_segment ℝ a b))
  obtain ⟨m₃, q₃, hq₃, hb₃, ha₃, hbb₃, hnone⟩ := hq₂.normalize_seam a b hab
    (by rw [hb₂, hb₁]; exact hsub) (hverts₂ ha) hb
  obtain ⟨q, hq, hqb, hqa, hqbb⟩ := hq₃.orient_seam a b
    (hq₃.seam_is_edge a b hab (by rw [hb₃, hb₂, hb₁]; exact hsub) ha₃ hbb₃ hnone)
  exact ⟨m₃, q, hq, hqb.trans (hb₃.trans (hb₂.trans hb₁)), hqa, hqbb⟩

end HolomorphicAnosov
