import HolomorphicAnosov.Topology.PolygonCycleData
import HolomorphicAnosov.Topology.PolygonDeleteVertexBoundary
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Subdivision of a simple polygon edge

Source context: Cairns (1951), preliminary §2(B), p.860. The finite subdivision
argument, implicit in the polygon gluing step, is agent-written.
DAG node: `topo.polygon_insert_vertex_g17`.

A point in an edge interior is not an old vertex: intersect its old outgoing edge
with that edge and use simplicity. Insert it immediately after the initial vertex.
Cyclic succession then replaces exactly one edge by its two subsegments. Their
union is the old edge, and their intersection is the inserted point. Intersections
with other edges are old common endpoints; an old endpoint beyond the inserted
point cannot lie in the wrong subsegment. All old vertices are retained, the new
vertex is distinct from them, and the boundary union is unchanged.
-/

namespace HolomorphicAnosov
open Set

lemma segment_split_at {a b x : ℂ} (hx : x ∈ segment ℝ a b) :
    segment ℝ a x ∪ segment ℝ x b = segment ℝ a b := by
  apply subset_antisymm
  · exact union_subset
      ((convex_segment a b).segment_subset (left_mem_segment ℝ a b) hx)
      ((convex_segment a b).segment_subset hx (right_mem_segment ℝ a b))
  · intro z hz
    rw [← insert_endpoints_openSegment] at hz
    rcases hz with rfl | rfl | hz
    · exact Or.inl (left_mem_segment ℝ _ _)
    · exact Or.inr (right_mem_segment ℝ _ _)
    have hline : x ∈ range (AffineMap.lineMap a b : ℝ → ℂ) := by
      rw [segment_eq_image_lineMap] at hx
      exact image_subset_range _ _ hx
    rcases openSegment_subset_union a b hline hz with rfl | hz | hz
    · exact Or.inl (right_mem_segment ℝ _ _)
    · exact Or.inl (openSegment_subset_segment ℝ _ _ hz)
    · exact Or.inr (openSegment_subset_segment ℝ _ _ hz)

lemma segment_split_inter {a b x : ℂ} (hx : x ∈ segment ℝ a b) :
    segment ℝ a x ∩ segment ℝ x b = {x} := by
  apply subset_antisymm
  · intro z hz
    have hax : Wbtw ℝ a x b := mem_segment_iff_wbtw.mp hx
    have haz : Wbtw ℝ a z x := mem_segment_iff_wbtw.mp hz.1
    have hzb : Wbtw ℝ x z b := mem_segment_iff_wbtw.mp hz.2
    have hxzb : Wbtw ℝ z x b := hax.trans_left_right haz
    exact hxzb.swap_left_iff.mp hzb
  · rintro z rfl
    exact ⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩


lemma PolygonCycleData.insert_vertex {n : ℕ} {p : Polygon ℂ (n + 2)}
    (h : PolygonCycleData p) (j : Fin (n + 2)) (x : ℂ)
    (hx : x ∈ openSegment ℝ (p j) (p (finRotate (n + 2) j))) :
    let q : Polygon ℂ (n + 3) := ⟨Fin.insertNth j.succ x p.vertices⟩
    PolygonCycleData q ∧ q.boundary ℝ = p.boundary ℝ ∧
      range p.vertices ⊆ range q.vertices ∧ x ∈ range q.vertices := by
  classical
  intro q
  let k := j.succ
  have hqk : q k = x := by simp [q, k]
  have hqold (i : Fin (n + 2)) : q (k.succAbove i) = p i :=
    by simp [q, k]
  have hbefore : k.succAbove j = j.castSucc := by
    apply Fin.ext
    simp [k, Fin.succAbove, Fin.lt_def]
  have hnext : finRotate (n + 3) (k.succAbove j) = k := by
    rw [hbefore]
    apply Fin.ext
    rw [coe_finRotate]
    split_ifs with he
    · have he' := congrArg Fin.val he
      simp only [Fin.val_castSucc, Fin.val_last] at he'
      omega
    · rfl
  have hnext' : k.succAbove (finRotate (n + 2) j) = finRotate (n + 3) k := by
    rw [Polygon.succAbove_finRotate, ite_eq_left hnext]
  have hnot (i : Fin (n + 2)) (hi : i ≠ j) :
      finRotate (n + 3) (k.succAbove i) ≠ k := by
    intro he
    exact hi (Fin.succAbove_right_injective ((finRotate (n + 3)).injective
      (he.trans hnext.symm)))
  have hsucc (i : Fin (n + 2)) (hi : i ≠ j) :
      k.succAbove (finRotate (n + 2) i) = finRotate (n + 3) (k.succAbove i) := by
    rw [Polygon.succAbove_finRotate, ite_eq_right (hnot i hi)]
  have hxseg := openSegment_subset_segment ℝ _ _ hx
  have hxnleft : x ≠ p j := by
    rintro rfl
    exact h.nondegenerate j (left_mem_openSegment_iff.mp hx)
  have hxnright : x ≠ p (finRotate (n + 2) j) := by
    rintro rfl
    exact h.nondegenerate j (right_mem_openSegment_iff.mp hx)
  have hxvertices (i : Fin (n + 2)) : x ≠ p i := by
    intro he
    have hv : p i ∈ p.edgeSet ℝ j := by
      simpa only [Polygon.edgeSet, affineSegment_eq_segment, he] using hxseg
    rcases (h.vertex_mem_edge i j).mp hv with rfl | rfl
    · exact hxnleft he
    · exact hxnright he
  have hqin : Function.Injective q.vertices := by
    intro u v huv
    by_cases hu : u = k
    · subst u
      by_cases hv : v = k
      · exact hv.symm
      obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hv
      exact (hxvertices i (by simpa only [hqk, hqold] using huv)).elim
    obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hu
    by_cases hv : v = k
    · subst v
      exact (hxvertices i (by simpa only [hqk, hqold] using huv.symm)).elim
    obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hv
    exact congrArg k.succAbove (h.injective (by simpa only [hqold] using huv))
  have hedge₀ : q.edgeSet ℝ k = segment ℝ x (p (finRotate (n + 2) j)) := by
    simp only [Polygon.edgeSet, affineSegment_eq_segment, hqk, ← hnext', hqold]
  have hedge₁ : q.edgeSet ℝ (k.succAbove j) = segment ℝ (p j) x := by
    simp only [Polygon.edgeSet, affineSegment_eq_segment, hqold, hnext, hqk]
  have hedge₂ (i : Fin (n + 2)) (hi : i ≠ j) :
      q.edgeSet ℝ (k.succAbove i) = p.edgeSet ℝ i := by
    simp only [Polygon.edgeSet, affineSegment_eq_segment, ← hsucc i hi, hqold]
  have hedge_sub (i : Fin (n + 2)) :
      q.edgeSet ℝ (k.succAbove i) ⊆ p.edgeSet ℝ i := by
    by_cases hi : i = j
    · subst i
      rw [hedge₁, Polygon.edgeSet, affineSegment_eq_segment]
      exact (convex_segment _ _).segment_subset (left_mem_segment ℝ _ _) hxseg
    · rw [hedge₂ i hi]
  have hedge₀_sub : q.edgeSet ℝ k ⊆ p.edgeSet ℝ j := by
    rw [hedge₀, Polygon.edgeSet, affineSegment_eq_segment]
    exact (convex_segment _ _).segment_subset hxseg (right_mem_segment ℝ _ _)
  have hright_not : p (finRotate (n + 2) j) ∉ q.edgeSet ℝ (k.succAbove j) := by
    rw [hedge₁]
    intro hb
    have hh := segment_split_inter hxseg
    have := (Set.ext_iff.mp hh (p (finRotate (n + 2) j))).mp
      ⟨hb, right_mem_segment ℝ _ _⟩
    exact hxnright this.symm
  have hleft_not : p j ∉ q.edgeSet ℝ k := by
    rw [hedge₀]
    intro ha
    have hh := segment_split_inter hxseg
    have := (Set.ext_iff.mp hh (p j)).mp ⟨left_mem_segment ℝ _ _, ha⟩
    exact hxnleft this.symm
  have hends_old (i : Fin (n + 2)) {z : ℂ}
      (hz : z ∈ q.edgeSet ℝ (k.succAbove i))
      (he : z ∈ ({p i, p (finRotate (n + 2) i)} : Set ℂ)) :
      z ∈ ({q (k.succAbove i), q (finRotate (n + 3) (k.succAbove i))} : Set ℂ) := by
    by_cases hi : i = j
    · subst i
      rcases he with rfl | he
      · simp only [hqold, mem_insert_iff, true_or]
      · exact (hright_not (he ▸ hz)).elim
    · simpa only [← hsucc i hi, hqold] using he
  have hends_new (i : Fin (n + 2)) {z : ℂ}
      (hz : z ∈ q.edgeSet ℝ k ∩ q.edgeSet ℝ (k.succAbove i)) :
      z ∈ ({q k, q (finRotate (n + 3) k)} : Set ℂ) ∩
        {q (k.succAbove i), q (finRotate (n + 3) (k.succAbove i))} := by
    by_cases hi : i = j
    · subst i
      have he : z = x := by
        have hh := segment_split_inter hxseg
        exact (Set.ext_iff.mp hh z).mp ⟨hedge₁ ▸ hz.2, hedge₀ ▸ hz.1⟩
      simp [he, hqk, hnext]
    · have he := h.simple j i (Ne.symm hi) ⟨hedge₀_sub hz.1, hedge_sub i hz.2⟩
      have hzright : z = p (finRotate (n + 2) j) := by
        rcases he.1 with he | he
        · exact (hleft_not (he ▸ hz.1)).elim
        · exact he
      refine ⟨?_, hends_old i hz.2 he.2⟩
      simp only [← hnext', hqold, hzright, mem_insert_iff, mem_singleton_iff, or_true]
  refine ⟨⟨hqin, ?_⟩, ?_, ?_, ⟨k, hqk⟩⟩
  · intro u v huv z hz
    by_cases hu : u = k
    · subst u
      obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq (Ne.symm huv)
      exact hends_new i hz
    obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hu
    by_cases hv : v = k
    · subst v
      exact (hends_new i ⟨hz.2, hz.1⟩).symm
    obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hv
    have hil : i ≠ l := fun he ↦ huv (congrArg k.succAbove he)
    have he := h.simple i l hil ⟨hedge_sub i hz.1, hedge_sub l hz.2⟩
    exact ⟨hends_old i hz.1 he.1, hends_old l hz.2 he.2⟩
  · apply subset_antisymm
    · apply iUnion_subset
      intro u
      by_cases hu : u = k
      · subst u
        exact hedge₀_sub.trans (subset_iUnion _ j)
      obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hu
      exact (hedge_sub i).trans (subset_iUnion _ i)
    · apply iUnion_subset
      intro i
      by_cases hi : i = j
      · subst i
        rw [Polygon.edgeSet, affineSegment_eq_segment, ← segment_split_at hxseg]
        exact union_subset (hedge₁ ▸ subset_iUnion _ (k.succAbove j))
          (hedge₀ ▸ subset_iUnion _ k)
      · rw [← hedge₂ i hi]
        exact subset_iUnion _ _
  · rintro z ⟨i, rfl⟩
    exact ⟨k.succAbove i, hqold i⟩

end HolomorphicAnosov
