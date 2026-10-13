import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Polygon.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Analysis.Convex.Between

/-!
# Closing a segment chain by a protected segment

Source: Cairns (1951), Lemma 3.1(B,C), pp.861–862 and Lemma 5.1, p.866.
This is the agent-written shortest-path detail of the omitted finite polygonal
assembly, extracted from the existing marked-segment closure proof.
-/
namespace HolomorphicAnosov
open Set

/-- If a segment chain joins v to w inside X, the closing segment meets X only
at its endpoints, and the closing segment is not contained in X, there is a
simple finite polygon made of that closing segment and segments in X.

Proof: form the graph with distinct vertices joined precisely when their segment
lies in X, and take a shortest path. Its vertices are distinct. Nonadjacent
intersecting edges admit a two-edge shortcut through their intersection, which
contradicts minimal length. Adjacent edges meeting beyond their common endpoint
are collinear and admit a one-edge shortcut. The same shortcut argument shows a
path vertex lies on an edge only when it is an endpoint. Close the path by [w,v].
The intersection assumption on X controls intersections with this last edge;
the no-direct-edge assumption ensures at least three vertices. Minimality also
excludes shortcuts across every two successive path edges, a property retained
for recognizing marked radial crossings in the round-disk application.
-/
theorem segment_chain_polygon_closure
    (X : Set ℂ) (v w : ℂ) (hvw : v ≠ w)
    (hXcentral : ∀ z ∈ X, z ∈ segment ℝ v w → z = v ∨ z = w)
    (hnot : ¬segment ℝ v w ⊆ X)
    (hXchain : Relation.ReflTransGen (fun a b ↦ segment ℝ a b ⊆ X) v w) :
    ∃ (n : ℕ) (p : Polygon ℂ (n + 3)),
      Function.Injective p.vertices ∧ p.HasNondegenerateEdges ∧
      (∀ i j : Fin (n + 3), i ≠ j →
        p.edgeSet ℝ i ∩ p.edgeSet ℝ j =
          ({p i, p (finRotate (n + 3) i)} ∩ {p j, p (finRotate (n + 3) j)})) ∧
      p 0 = v ∧ p (Fin.last (n + 2)) = w ∧
      (∀ i : Fin (n + 3), i ≠ Fin.last (n + 2) → p.edgeSet ℝ i ⊆ X) ∧
      (∀ i j : Fin (n + 3), i.val + 2 = j.val → ¬segment ℝ (p i) (p j) ⊆ X) := by
  classical
  let G : SimpleGraph ℂ := {
    Adj := fun a b ↦ a ≠ b ∧ segment ℝ a b ⊆ X
    symm := ⟨fun a b h ↦ ⟨h.1.symm, by simpa only [segment_symm] using h.2⟩⟩
    loopless := ⟨fun a h ↦ h.1 rfl⟩ }
  have hreach : G.Reachable v w := by
    have hmap : ∀ b, Relation.ReflTransGen (fun a b ↦ segment ℝ a b ⊆ X) v b →
        G.Reachable v b := by
      intro b hb
      induction hb with
      | refl => exact .rfl
      | @tail b c hprev hbc ih =>
        by_cases h : b = c
        · subst c
          exact ih
        · exact ih.trans (SimpleGraph.Adj.reachable (show G.Adj b c from ⟨h, hbc⟩))
    exact hmap w hXchain
  obtain ⟨q, hqpath, hqdist⟩ := hreach.exists_path_of_dist
  have hstep (a b : ℂ) (hab : segment ℝ a b ⊆ X) :
      ∃ r : G.Walk a b, r.length ≤ 1 := by
    by_cases h : a = b
    · subst b
      exact ⟨.nil, by simp⟩
    · exact ⟨(show G.Adj a b from ⟨h, hab⟩).toWalk, by simp⟩
  have hbound (i j : ℕ) (hi : i ≤ q.length) (hj : j ≤ q.length)
      (r : G.Walk (q.getVert i) (q.getVert j)) : j ≤ i + r.length := by
    have hmin := G.dist_le (((q.take i).append r).append (q.drop j))
    rw [← hqdist, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length, Nat.min_eq_left hi] at hmin
    omega
  have hfar (i j : ℕ) (hi : i < q.length) (hj : j < q.length) (hij : i + 1 < j) :
      Disjoint (segment ℝ (q.getVert i) (q.getVert (i + 1)))
        (segment ℝ (q.getVert j) (q.getVert (j + 1))) := by
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    obtain ⟨r₁, hr₁⟩ := hstep (q.getVert i) z
      (((convex_segment _ _).segment_subset (left_mem_segment ℝ _ _) hzi).trans
        (q.adj_getVert_succ hi).2)
    obtain ⟨r₂, hr₂⟩ := hstep z (q.getVert (j + 1))
      (((convex_segment _ _).segment_subset hzj (right_mem_segment ℝ _ _)).trans
        (q.adj_getVert_succ hj).2)
    have h := hbound i (j + 1) hi.le (by omega) (r₁.append r₂)
    simp only [SimpleGraph.Walk.length_append] at h
    omega
  have hnear (i : ℕ) (hi : i + 1 < q.length) :
      segment ℝ (q.getVert i) (q.getVert (i + 1)) ∩
        segment ℝ (q.getVert (i + 1)) (q.getVert (i + 2)) ⊆ {q.getVert (i + 1)} := by
    rintro z ⟨hza, hzc⟩
    by_contra hzb
    have hcol₁ := (mem_segment_iff_wbtw.mp hza).collinear
    have hcol₂ := (mem_segment_iff_wbtw.mp hzc).collinear
    have ha : q.getVert i ∈ line[ℝ, q.getVert (i + 1), z] :=
      hcol₁.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) (Ne.symm hzb)
    have hc : q.getVert (i + 2) ∈ line[ℝ, q.getVert (i + 1), z] :=
      hcol₂.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) (Ne.symm hzb)
    have hcol : Collinear ℝ ({q.getVert i, q.getVert (i + 1), q.getVert (i + 2)} : Set ℂ) :=
      collinear_triple_of_mem_affineSpan_pair ha (left_mem_affineSpan_pair ℝ _ _) hc
    have hac : q.getVert i ≠ q.getVert (i + 2) := by
      intro h
      have := hqpath.getVert_injOn (show i ≤ q.length by omega)
        (show i + 2 ≤ q.length by omega) h
      omega
    have hb : q.getVert (i + 1) ∈ line[ℝ, q.getVert i, q.getVert (i + 2)] :=
      hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hac
    obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hb
    have hseg : segment ℝ (q.getVert i) (q.getVert (i + 2)) ⊆ X := by
      intro y hy
      rw [← insert_endpoints_openSegment] at hy
      rcases hy with rfl | rfl | hy
      · exact (q.adj_getVert_succ (show i < q.length by omega)).2
          (left_mem_segment ℝ _ _)
      · exact (q.adj_getVert_succ hi).2 (right_mem_segment ℝ _ _)
      · rcases openSegment_subset_union _ _ ⟨r, hr⟩ hy with rfl | hy | hy
        · exact (q.adj_getVert_succ hi).2 (left_mem_segment ℝ _ _)
        · exact (q.adj_getVert_succ (show i < q.length by omega)).2
            (openSegment_subset_segment ℝ _ _ hy)
        · exact (q.adj_getVert_succ hi).2 (openSegment_subset_segment ℝ _ _ hy)
    obtain ⟨r, hr⟩ := hstep _ _ hseg
    have := hbound i (i + 2) (by omega) (by omega) r
    omega
  have hvertex (i k : ℕ) (hi : i < q.length) (hk : k ≤ q.length)
      (hki : q.getVert k ∈ segment ℝ (q.getVert i) (q.getVert (i + 1))) :
      k = i ∨ k = i + 1 := by
    obtain ⟨r₁, hr₁⟩ := hstep (q.getVert i) (q.getVert k)
      (((convex_segment _ _).segment_subset (left_mem_segment ℝ _ _) hki).trans
        (q.adj_getVert_succ hi).2)
    obtain ⟨r₂, hr₂⟩ := hstep (q.getVert k) (q.getVert (i + 1))
      (((convex_segment _ _).segment_subset hki (right_mem_segment ℝ _ _)).trans
        (q.adj_getVert_succ hi).2)
    have h₁ := hbound i k hi.le hk r₁
    have h₂ := hbound k (i + 1) hk (by omega) r₂
    omega
  have hlen : 2 ≤ q.length := by
    have h := hreach.one_lt_dist_of_ne_of_not_adj hvw (fun hadj ↦ hnot hadj.2)
    omega
  obtain ⟨n, hn⟩ : ∃ n, q.length = n + 2 := ⟨q.length - 2, by omega⟩
  let p : Polygon ℂ (n + 3) := ⟨fun i ↦ q.getVert i.val⟩
  have hpinj : Function.Injective p.vertices := by
    intro i j hij
    apply Fin.ext
    exact hqpath.getVert_injOn (show i.val ≤ q.length by omega)
      (show j.val ≤ q.length by omega) hij
  have hpnondeg : p.HasNondegenerateEdges := by
    intro i heq
    have heq' := congrArg Fin.val (hpinj heq)
    by_cases hi : i = Fin.last (n + 2)
    · subst i
      simp only [finRotate_last, Fin.val_last, Fin.val_zero] at heq'
      omega
    · rw [coe_finRotate_of_ne_last hi] at heq'
      omega
  have hpzero : p 0 = v := q.getVert_zero
  have hplast : p (Fin.last (n + 2)) = w := by
    change q.getVert (n + 2) = w
    rw [← hn]
    exact q.getVert_length
  have hlastedge : p.edgeSet ℝ (Fin.last (n + 2)) = segment ℝ w v := by
    simp only [Polygon.edgeSet, finRotate_last, hplast, hpzero, affineSegment_eq_segment]
  have hedge (i : Fin (n + 3)) (hi : i ≠ Fin.last (n + 2)) :
      p.edgeSet ℝ i = segment ℝ (q.getVert i.val) (q.getVert (i.val + 1)) := by
    simp only [Polygon.edgeSet, affineSegment_eq_segment, p, coe_finRotate_of_ne_last hi]
  have hothers (i : Fin (n + 3)) (hi : i ≠ Fin.last (n + 2)) : p.edgeSet ℝ i ⊆ X := by
    rw [hedge i hi]
    exact (q.adj_getVert_succ (by have := Fin.val_lt_last hi; omega)).2
  have hinter_lt (i j : Fin (n + 3)) (hij : i.val < j.val) :
      p.edgeSet ℝ i ∩ p.edgeSet ℝ j ⊆
        ({p i, p (finRotate (n + 3) i)} : Set ℂ) ∩ {p j, p (finRotate (n + 3) j)} := by
    have hi : i ≠ Fin.last (n + 2) := by intro h; subst i; have := j.isLt; simp_all; omega
    have hiq : i.val < q.length := by have := Fin.val_lt_last hi; omega
    rintro z ⟨hzi, hzj⟩
    by_cases hj : j = Fin.last (n + 2)
    · subst j
      rw [hlastedge, segment_symm] at hzj
      rcases hXcentral z (hothers i hi hzi) hzj with hzv | hzw
      · subst z
        have hi0 : i.val = 0 := by
          have h := hvertex i.val 0 hiq (by omega)
            (by simpa only [q.getVert_zero, ← hedge i hi] using hzi)
          omega
        have hiv : p i = v := by change q.getVert i.val = v; rw [hi0, q.getVert_zero]
        simp only [finRotate_last, hplast, hpzero, mem_inter_iff, mem_insert_iff,
          mem_singleton_iff]
        exact ⟨Or.inl hiv.symm, Or.inr trivial⟩
      · subst z
        have hiL : i.val + 1 = q.length := by
          have h := hvertex i.val q.length hiq le_rfl
            (by simpa only [q.getVert_length, ← hedge i hi] using hzi)
          omega
        have hiw : p (finRotate (n + 3) i) = w := by
          change q.getVert (finRotate (n + 3) i).val = w
          rw [coe_finRotate_of_ne_last hi, hiL, q.getVert_length]
        simp only [finRotate_last, hplast, hpzero, mem_inter_iff, mem_insert_iff,
          mem_singleton_iff]
        exact ⟨Or.inr hiw.symm, Or.inl trivial⟩
    · have hjq : j.val < q.length := by have := Fin.val_lt_last hj; omega
      by_cases hgap : i.val + 1 < j.val
      · exact (Set.disjoint_left.mp (hfar i.val j.val hiq hjq hgap)
          (hedge i hi ▸ hzi) (hedge j hj ▸ hzj)).elim
      · have hnext : j.val = i.val + 1 := by omega
        have hz : z = q.getVert (i.val + 1) := hnear i.val (by omega)
          ⟨hedge i hi ▸ hzi, by simpa only [hedge j hj, hnext, Nat.add_assoc] using hzj⟩
        have hrot : p (finRotate (n + 3) i) = q.getVert (i.val + 1) := by
          change q.getVert (finRotate (n + 3) i).val = _
          rw [coe_finRotate_of_ne_last hi]
        have hjval : p j = q.getVert (i.val + 1) := congrArg q.getVert hnext
        exact ⟨Or.inr (hz.trans hrot.symm), Or.inl (hz.trans hjval.symm)⟩
  have hinter (i j : Fin (n + 3)) (hij : i ≠ j) :
      p.edgeSet ℝ i ∩ p.edgeSet ℝ j =
        ({p i, p (finRotate (n + 3) i)} : Set ℂ) ∩ {p j, p (finRotate (n + 3) j)} := by
    apply subset_antisymm
    · rcases lt_trichotomy i.val j.val with h | h | h
      · exact hinter_lt i j h
      · exact (hij (Fin.ext h)).elim
      · simpa only [inter_comm] using hinter_lt j i h
    · rintro z ⟨hi, hj⟩
      simp only [Polygon.edgeSet, affineSegment_eq_segment]
      constructor
      · rcases hi with rfl | rfl
        · exact left_mem_segment ℝ _ _
        · exact right_mem_segment ℝ _ _
      · rcases hj with rfl | rfl
        · exact left_mem_segment ℝ _ _
        · exact right_mem_segment ℝ _ _
  refine ⟨n, p, hpinj, hpnondeg, hinter, hpzero, hplast, hothers, ?_⟩
  intro i j hij hseg
  obtain ⟨r, hr⟩ := hstep (p i) (p j) hseg
  have hb := hbound i.val j.val (by have := i.isLt; omega)
    (by have := j.isLt; omega) r
  omega

end HolomorphicAnosov
