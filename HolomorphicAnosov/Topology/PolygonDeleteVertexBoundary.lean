import Mathlib.Geometry.Polygon.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Tactic.SplitIfs

open Set

theorem Polygon.succAbove_finRotate {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    i.succAbove (finRotate (n + 1) j) =
      if finRotate (n + 2) (i.succAbove j) = i then finRotate (n + 2) i
      else finRotate (n + 2) (i.succAbove j) := by
  have hs (k : Fin (n + 1)) : (i.succAbove k).val =
      if k.val < i.val then k.val else k.val + 1 := by
    simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
    split <;> rfl
  have hr (k : Fin (n + 2)) : (finRotate (n + 2) k).val =
      if k.val = n + 1 then 0 else k.val + 1 := by
    simp only [coe_finRotate, Fin.ext_iff, Fin.val_last]
  have hrj : (finRotate (n + 1) j).val =
      if j.val = n then 0 else j.val + 1 := by
    simp only [coe_finRotate, Fin.ext_iff, Fin.val_last]
  have hs₁ := hs j
  have hs₂ := hs (finRotate (n + 1) j)
  have hr₁ := hr (i.succAbove j)
  have hr₂ := hr i
  by_cases h : finRotate (n + 2) (i.succAbove j) = i
  · rw [ite_eq_left h]
    apply Fin.ext
    have hv := congrArg Fin.val h
    split_ifs at hs₁ hs₂ hr₁ hr₂ hrj <;> omega
  · rw [ite_eq_right h]
    apply Fin.ext
    have hv : (finRotate (n + 2) (i.succAbove j)).val ≠ i.val :=
      fun he ↦ h (Fin.ext he)
    split_ifs at hs₁ hs₂ hr₁ hr₂ hrj <;> omega

namespace HolomorphicAnosov

/-- Deleting a cyclic polygon vertex preserves the boundary if the two adjacent
segments have union equal to the direct segment between its neighbours.

Source: the redundant-vertex reduction used in Cairns (1951), Theorem 2.1,
printed pp.860–861; the finite indexing verification is supplied here.
DAG node: `topo.polygon_boundary_delete_vertex_g12`.

Proof: every retained vertex starts its old edge except the predecessor of the
removed vertex, whose new edge is exactly the union of the two old adjacent
edges. The order-preserving enumeration of the remaining vertices skips the
removed vertex, including across the cyclic wrap. Thus every new edge is in
the old boundary, every old nonremoved edge occurs in a new edge, and the
removed outgoing edge occurs in the joined edge. Taking unions proves equality.
The assumption that at least two vertices precede deletion is sufficient;
no simplicity or nondegeneracy assumption is needed. -/
theorem polygon_boundary_delete_vertex {V : Type*} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (hn : 0 < n) (p : Polygon V (n + 1)) (i : Fin (n + 1))
    (hjoin : segment ℝ (p ((finRotate (n + 1)).symm i)) (p i) ∪
        segment ℝ (p i) (p (finRotate (n + 1) i)) =
      segment ℝ (p ((finRotate (n + 1)).symm i)) (p (finRotate (n + 1) i))) :
    (Polygon.mk (fun j : Fin n ↦ p (i.succAbove j))).boundary ℝ = p.boundary ℝ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let q : Polygon V (n + 1) := ⟨fun j ↦ p (i.succAbove j)⟩
  have hedge (j : Fin (n + 1)) : q.edgeSet ℝ j =
      if finRotate (n + 2) (i.succAbove j) = i then
        p.edgeSet ℝ (i.succAbove j) ∪ p.edgeSet ℝ i
      else p.edgeSet ℝ (i.succAbove j) := by
    simp only [Polygon.edgeSet, affineSegment_eq_segment]
    change segment ℝ (p (i.succAbove j)) (p (i.succAbove (finRotate (n + 1) j))) = _
    rw [Polygon.succAbove_finRotate]
    split_ifs with h
    · have hj : i.succAbove j = (finRotate (n + 2)).symm i := by
        apply (finRotate (n + 2)).injective
        simpa using h
      simp only [hj, Equiv.apply_symm_apply]
      exact hjoin.symm
    · rfl
  have hsub (j : Fin (n + 1)) : p.edgeSet ℝ (i.succAbove j) ⊆ q.edgeSet ℝ j := by
    rw [hedge]
    split_ifs
    · exact subset_union_left
    · exact Subset.rfl
  have hprev : (finRotate (n + 2)).symm i ≠ i := by
    intro he
    have hr : finRotate (n + 2) i = i := by
      simpa only [Equiv.apply_symm_apply] using (congrArg (finRotate (n + 2)) he).symm
    have hv := congrArg Fin.val hr
    rw [coe_finRotate] at hv
    split_ifs at hv with hi
    · subst i
      simp only [Fin.val_last] at hv
      omega
    · omega
  obtain ⟨j₀, hj₀⟩ := Fin.exists_succAbove_eq hprev
  change q.boundary ℝ = p.boundary ℝ
  apply Subset.antisymm
  · apply iUnion_subset
    intro j
    rw [hedge]
    split_ifs
    · exact union_subset (subset_iUnion (p.edgeSet ℝ) _) (subset_iUnion (p.edgeSet ℝ) _)
    · exact subset_iUnion (p.edgeSet ℝ) _
  · apply iUnion_subset
    intro k
    by_cases hk : k = i
    · subst k
      apply Subset.trans _ (subset_iUnion (q.edgeSet ℝ) j₀)
      rw [hedge, hj₀, Equiv.apply_symm_apply, ite_eq_left rfl]
      exact subset_union_right
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
      exact (hsub j).trans (subset_iUnion (q.edgeSet ℝ) j)

end HolomorphicAnosov
