import Mathlib.Geometry.Polygon.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs

/-! # Simplicity after deleting a redundant polygon vertex

Source: Cairns (1951), Theorem 2.1, pp.860–861, redundant-collinear-vertex
reduction. The finite indexing and intersection verification is agent-written.
-/

open Set

namespace HolomorphicAnosov

/-- Deleting a vertex lying strictly between its neighbours preserves the
finite vertex and edge-intersection conditions of a simple closed polygon.

Source: Cairns, *An Elementary Proof of the Jordan-Schoenflies Theorem* (1951),
Theorem 2.1, pp.860–861; explicit elementary verification of the redundant
vertex reduction. Proof: the remaining cyclic enumeration skips the deleted
index. Every edge is unchanged except its predecessor's edge, which is the
union of the two old adjacent edges. An old polygon vertex on an old edge is
one of its endpoints, by applying simplicity to its own outgoing edge. Hence
the deleted vertex lies on no other old edge. Intersecting a joined edge with
an unchanged edge therefore gives only retained endpoints; intersecting two
unchanged edges has the same property by the original simplicity condition.
Both new edges cannot be joined edges since cyclic succession is injective.
Vertex injectivity is inherited by the remaining enumeration. A simple
triangle cannot have the deleted vertex between its neighbours, since it
would lie in the third edge without being an endpoint; hence at least three
vertices remain. Distinct cyclic successors then give nonzero new edges. -/
theorem polygon_delete_vertex_simplicity {V : Type*}
    [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (p : Polygon V (n + 2)) (i : Fin (n + 2))
    (hn : 3 ≤ n + 2) (hinj : Function.Injective p.vertices)
    (hsimple : ∀ j k : Fin (n + 2), j ≠ k →
      p.edgeSet ℝ j ∩ p.edgeSet ℝ k ⊆
        p.vertices '' ({j, finRotate (n + 2) j} ∩ {k, finRotate (n + 2) k}))
    (hbetween : p i ∈ openSegment ℝ (p ((finRotate (n + 2)).symm i))
      (p (finRotate (n + 2) i)))
    (hjoin : segment ℝ (p ((finRotate (n + 2)).symm i)) (p i) ∪
        segment ℝ (p i) (p (finRotate (n + 2) i)) =
      segment ℝ (p ((finRotate (n + 2)).symm i)) (p (finRotate (n + 2) i))) :
    let q : Polygon V (n + 1) := ⟨fun j ↦ p (i.succAbove j)⟩
    3 ≤ n + 1 ∧ Function.Injective q.vertices ∧ q.HasNondegenerateEdges ∧
      ∀ j k : Fin (n + 1), j ≠ k →
        q.edgeSet ℝ j ∩ q.edgeSet ℝ k ⊆
          q.vertices '' ({j, finRotate (n + 1) j} ∩ {k, finRotate (n + 1) k}) := by
  classical
  intro q
  have hvertex (j k : Fin (n + 2)) (h : p j ∈ p.edgeSet ℝ k) :
      j = k ∨ j = finRotate (n + 2) k := by
    by_cases hjk : j = k
    · exact Or.inl hjk
    have hj : p j ∈ p.edgeSet ℝ j := left_mem_affineSegment ℝ _ _
    obtain ⟨l, hl, hlj⟩ := hsimple j k hjk ⟨hj, h⟩
    have hlj' : l = j := hinj hlj
    subst l
    simpa only [mem_insert_iff, mem_singleton_iff] using hl.2
  have hcount : 3 ≤ n + 1 := by
    by_contra h
    have he : n = 1 := by omega
    subst n
    have hmem : p i ∈ p.edgeSet ℝ (finRotate 3 i) := by
      simp only [Polygon.edgeSet, affineSegment_eq_segment]
      rw [segment_symm]
      have hr : finRotate 3 (finRotate 3 i) = (finRotate 3).symm i := by
        fin_cases i <;> decide
      rw [hr]
      exact openSegment_subset_segment ℝ _ _ hbetween
    have hend := hvertex i (finRotate 3 i) hmem
    fin_cases i <;> norm_num [finRotate_apply] at hend
  have hskip (j : Fin (n + 1)) : i.succAbove (finRotate (n + 1) j) =
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
  have hedge (j : Fin (n + 1)) : q.edgeSet ℝ j =
      if finRotate (n + 2) (i.succAbove j) = i then
        p.edgeSet ℝ (i.succAbove j) ∪ p.edgeSet ℝ i
      else p.edgeSet ℝ (i.succAbove j) := by
    simp only [Polygon.edgeSet, affineSegment_eq_segment]
    change segment ℝ (p (i.succAbove j)) (p (i.succAbove (finRotate (n + 1) j))) = _
    rw [hskip]
    split_ifs with h
    · have hj : i.succAbove j = (finRotate (n + 2)).symm i := by
        apply (finRotate (n + 2)).injective
        simpa using h
      simp only [hj, Equiv.apply_symm_apply]
      exact hjoin.symm
    · rfl
  have hqinj : Function.Injective q.vertices := hinj.comp (Fin.succAbove_right_injective)
  have hqnondeg : q.HasNondegenerateEdges := by
    intro j he
    have hj := hqinj he
    have hv := congrArg Fin.val hj
    rw [coe_finRotate] at hv
    split_ifs at hv with hjlast
    · subst j
      simp only [Fin.val_last] at hv
      omega
    · omega
  have hold (j k : Fin (n + 2)) (hjk : j ≠ k) {z : V}
      (hz : z ∈ p.edgeSet ℝ j ∩ p.edgeSet ℝ k) :
      (z = p j ∨ z = p (finRotate (n + 2) j)) ∧
      (z = p k ∨ z = p (finRotate (n + 2) k)) := by
    obtain ⟨l, hl, rfl⟩ := hsimple j k hjk hz
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff] at hl
    exact ⟨hl.1.elim (fun h ↦ Or.inl (congrArg p h))
      (fun h ↦ Or.inr (congrArg p h)),
      hl.2.elim (fun h ↦ Or.inl (congrArg p h))
      (fun h ↦ Or.inr (congrArg p h))⟩
  have hends (j k : Fin (n + 1)) (hjk : j ≠ k) {z : V}
      (hz : z ∈ q.edgeSet ℝ j ∩ q.edgeSet ℝ k)
      (hk : finRotate (n + 2) (i.succAbove k) ≠ i) :
      (z = q j ∨ z = q (finRotate (n + 1) j)) ∧
      (z = q k ∨ z = q (finRotate (n + 1) k)) := by
    have hzK : z ∈ p.edgeSet ℝ (i.succAbove k) := by
      simpa only [hedge, ite_eq_right hk] using hz.2
    have hzi : z ≠ p i := by
      intro he
      have h := hvertex i (i.succAbove k) (he ▸ hzK)
      exact h.elim (fun h ↦ Fin.succAbove_ne i k h.symm) (fun h ↦ hk h.symm)
    have hskipK := hskip k
    rw [ite_eq_right hk] at hskipK
    by_cases hj : finRotate (n + 2) (i.succAbove j) = i
    · have hzJ : z ∈ p.edgeSet ℝ (i.succAbove j) ∪ p.edgeSet ℝ i := by
        simpa only [hedge, ite_eq_left hj] using hz.1
      have hskipJ := hskip j
      rw [ite_eq_left hj] at hskipJ
      rcases hzJ with hzJ | hzJ
      · obtain ⟨hzj, hzk⟩ := hold (i.succAbove j) (i.succAbove k)
          (fun h ↦ hjk (Fin.succAbove_right_injective h)) ⟨hzJ, hzK⟩
        rw [hj] at hzj
        exact ⟨Or.inl (hzj.resolve_right hzi), by simpa only [q, ← hskipK] using hzk⟩
      · obtain ⟨hzj, hzk⟩ := hold i (i.succAbove k) (Fin.succAbove_ne i k).symm
          ⟨hzJ, hzK⟩
        exact ⟨Or.inr (by simpa only [q, ← hskipJ] using hzj.resolve_left hzi),
          by simpa only [q, ← hskipK] using hzk⟩
    · have hzJ : z ∈ p.edgeSet ℝ (i.succAbove j) := by
        simpa only [hedge, ite_eq_right hj] using hz.1
      have hskipJ := hskip j
      rw [ite_eq_right hj] at hskipJ
      obtain ⟨hzj, hzk⟩ := hold (i.succAbove j) (i.succAbove k)
        (fun h ↦ hjk (Fin.succAbove_right_injective h)) ⟨hzJ, hzK⟩
      exact ⟨by simpa only [q, ← hskipJ] using hzj,
        by simpa only [q, ← hskipK] using hzk⟩
  refine ⟨hcount, hqinj, hqnondeg, ?_⟩
  intro j k hjk z hz
  have he : (z = q j ∨ z = q (finRotate (n + 1) j)) ∧
      (z = q k ∨ z = q (finRotate (n + 1) k)) := by
    by_cases hk : finRotate (n + 2) (i.succAbove k) = i
    · have hj : finRotate (n + 2) (i.succAbove j) ≠ i := by
        intro hj
        exact hjk (Fin.succAbove_right_injective ((finRotate (n + 2)).injective
          (hj.trans hk.symm)))
      exact (hends k j hjk.symm ⟨hz.2, hz.1⟩ hj).symm
    · exact hends j k hjk hz hk
  rcases he.1 with hzj | hzj
  · refine ⟨j, ⟨by simp, ?_⟩, hzj.symm⟩
    simpa only [mem_insert_iff, mem_singleton_iff] using
      he.2.imp (fun h ↦ hqinj (hzj.symm.trans h)) (fun h ↦ hqinj (hzj.symm.trans h))
  · refine ⟨finRotate (n + 1) j, ⟨by simp, ?_⟩, hzj.symm⟩
    simpa only [mem_insert_iff, mem_singleton_iff] using
      he.2.imp (fun h ↦ hqinj (hzj.symm.trans h)) (fun h ↦ hqinj (hzj.symm.trans h))

end HolomorphicAnosov

