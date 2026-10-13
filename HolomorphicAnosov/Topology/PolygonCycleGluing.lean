import HolomorphicAnosov.Topology.PolygonCycleData
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Gluing polygon cycles along their last edges

Source context: Cairns (1951), preliminary §2(B), p.860. The explicit finite list
construction is agent-written. DAG node: `topo.polygon_glue_standard_g17`.

Let the first polygon start at a and end at b, and the second start at b and end
at a. Append their vertex lists with each final vertex omitted. At either join,
the successor is the first vertex of the other list, equal to the omitted endpoint.
Thus the new edges are precisely the nonfinal edges of both original polygons.
The retained vertex lists are disjoint: a shared retained vertex is on the seam,
so simplicity makes it a seam endpoint; the first list omits b and the second
omits a, a contradiction. Edges from one polygon retain their intersection property.
Edges from different polygons meet only on the seam, and simplicity against the
old final edge makes these points endpoints of both retained edges. Nonfinal edges
avoid the open seam. Conversely every original boundary point outside the open seam
is on a retained edge, or is a seam endpoint, each of which is a retained vertex.
This proves exactly the asserted boundary equality.
-/

namespace HolomorphicAnosov
open Set

lemma PolygonCycleData.glue_standard {n₁ n₂ : ℕ}
    (p : Polygon ℂ (n₁ + 3)) (q : Polygon ℂ (n₂ + 3))
    (hp : PolygonCycleData p) (hq : PolygonCycleData q)
    (a b : ℂ) (hab : a ≠ b)
    (hp0 : p 0 = a) (hplast : p (Fin.last (n₁ + 2)) = b)
    (hq0 : q 0 = b) (hqlast : q (Fin.last (n₂ + 2)) = a)
    (hinter : p.boundary ℝ ∩ q.boundary ℝ = segment ℝ a b) :
    ∃ r : Polygon ℂ ((n₁ + 2) + (n₂ + 2)), PolygonCycleData r ∧
      r.boundary ℝ = (p.boundary ℝ ∪ q.boundary ℝ) \ openSegment ℝ a b := by
  classical
  let r : Polygon ℂ ((n₁ + 2) + (n₂ + 2)) :=
    ⟨Fin.append (fun i : Fin (n₁ + 2) ↦ p i.castSucc)
      (fun i : Fin (n₂ + 2) ↦ q i.castSucc)⟩
  let L : Fin (n₁ + 2) → Fin ((n₁ + 2) + (n₂ + 2)) := Fin.castAdd (n₂ + 2)
  let R : Fin (n₂ + 2) → Fin ((n₁ + 2) + (n₂ + 2)) := Fin.natAdd (n₁ + 2)
  have hL (i : Fin (n₁ + 2)) : r (L i) = p i.castSucc := by simp [r, L]
  have hR (i : Fin (n₂ + 2)) : r (R i) = q i.castSucc := by simp [r, R]
  have hpnext (i : Fin (n₁ + 2)) : finRotate (n₁ + 3) i.castSucc = i.succ := by
    apply Fin.ext
    rw [coe_finRotate_of_ne_last (Fin.castSucc_ne_last i)]
    rfl
  have hqnext (i : Fin (n₂ + 2)) : finRotate (n₂ + 3) i.castSucc = i.succ := by
    apply Fin.ext
    rw [coe_finRotate_of_ne_last (Fin.castSucc_ne_last i)]
    rfl
  have hrval (i : Fin ((n₁ + 2) + (n₂ + 2))) :
      (finRotate ((n₁ + 2) + (n₂ + 2)) i).val =
        if i.val = (n₁ + 2) + (n₂ + 1) then 0 else i.val + 1 := by
    have hv := coe_finRotate (n := (n₁ + 2) + (n₂ + 1)) i
    change (finRotate ((n₁ + 2) + (n₂ + 2)) i).val = _ at hv
    simpa only [Fin.ext_iff, Fin.val_last] using hv
  have hLs (i : Fin (n₁ + 2)) :
      r (finRotate ((n₁ + 2) + (n₂ + 2)) (L i)) = p i.succ := by
    by_cases hi : i = Fin.last (n₁ + 1)
    · subst i
      have he : finRotate ((n₁ + 2) + (n₂ + 2)) (L (Fin.last (n₁ + 1))) = R 0 := by
        apply Fin.ext
        have hv := hrval (L (Fin.last (n₁ + 1)))
        simp only [L, Fin.val_castAdd, Fin.val_last] at hv
        rw [ite_eq_right (by omega)] at hv
        simpa only [R, Fin.val_natAdd, Fin.val_zero, Nat.add_zero] using hv
      rw [he, hR]
      simp only [Fin.castSucc_zero, Fin.succ_last, hq0, hplast]
    · have he : finRotate ((n₁ + 2) + (n₂ + 2)) (L i) =
          L (finRotate (n₁ + 2) i) := by
        apply Fin.ext
        have hv := hrval (L i)
        simp only [L, Fin.val_castAdd] at hv
        rw [ite_eq_right (by omega)] at hv
        simpa only [L, Fin.val_castAdd, coe_finRotate_of_ne_last hi] using hv
      rw [he, hL]
      congr 1
      apply Fin.ext
      simp only [Fin.val_castSucc, coe_finRotate_of_ne_last hi, Fin.val_succ]
  have hRs (i : Fin (n₂ + 2)) :
      r (finRotate ((n₁ + 2) + (n₂ + 2)) (R i)) = q i.succ := by
    by_cases hi : i = Fin.last (n₂ + 1)
    · subst i
      have he : finRotate ((n₁ + 2) + (n₂ + 2)) (R (Fin.last (n₂ + 1))) = L 0 := by
        have hh : R (Fin.last (n₂ + 1)) = Fin.last ((n₁ + 2) + (n₂ + 1)) := by
          apply Fin.ext
          simp [R]
        rw [hh]
        exact finRotate_last
      rw [he, hL]
      simp only [Fin.castSucc_zero, Fin.succ_last, hp0, hqlast]
    · have he : finRotate ((n₁ + 2) + (n₂ + 2)) (R i) =
          R (finRotate (n₂ + 2) i) := by
        apply Fin.ext
        have hv := hrval (R i)
        simp only [R, Fin.val_natAdd] at hv
        have hvi : i.val ≠ n₂ + 1 := by simpa only [Fin.ext_iff, Fin.val_last] using hi
        rw [ite_eq_right (by omega)] at hv
        simpa only [R, Fin.val_natAdd, coe_finRotate_of_ne_last hi, Nat.add_assoc] using hv
      rw [he, hR]
      congr 1
      apply Fin.ext
      simp only [Fin.val_castSucc, coe_finRotate_of_ne_last hi, Fin.val_succ]
  have hLe (i : Fin (n₁ + 2)) : r.edgeSet ℝ (L i) = p.edgeSet ℝ i.castSucc := by
    simp only [Polygon.edgeSet, hL, hLs, hpnext]
  have hRe (i : Fin (n₂ + 2)) : r.edgeSet ℝ (R i) = q.edgeSet ℝ i.castSucc := by
    simp only [Polygon.edgeSet, hR, hRs, hqnext]
  have hpseam : p.edgeSet ℝ (Fin.last (n₁ + 2)) = segment ℝ a b := by
    simp only [Polygon.edgeSet, affineSegment_eq_segment, finRotate_last, hplast, hp0]
    exact segment_symm ℝ _ _
  have hqseam : q.edgeSet ℝ (Fin.last (n₂ + 2)) = segment ℝ a b := by
    simp only [Polygon.edgeSet, affineSegment_eq_segment, finRotate_last, hqlast, hq0]
  have hcross (i : Fin (n₁ + 2)) (j : Fin (n₂ + 2)) :
      p i.castSucc ≠ q j.castSucc := by
    intro he
    have hm : p i.castSucc ∈ segment ℝ a b := by
      rw [← hinter]
      exact ⟨mem_iUnion.mpr ⟨i.castSucc, left_mem_affineSegment ℝ _ _⟩,
        he ▸ mem_iUnion.mpr ⟨j.castSucc, left_mem_affineSegment ℝ _ _⟩⟩
    have hpi := (hp.vertex_mem_edge i.castSucc (Fin.last (n₁ + 2))).mp (hpseam ▸ hm)
    have hqj := (hq.vertex_mem_edge j.castSucc (Fin.last (n₂ + 2))).mp
      (hqseam ▸ (he ▸ hm))
    have hi : i.castSucc = 0 := by
      simpa only [finRotate_last] using hpi.resolve_left (Fin.castSucc_ne_last i)
    have hj : j.castSucc = 0 := by
      simpa only [finRotate_last] using hqj.resolve_left (Fin.castSucc_ne_last j)
    exact hab (by simpa only [hi, hj, hp0, hq0] using he)
  have hrij : Function.Injective r.vertices := by
    intro i j hij
    induction i using Fin.addCases with
    | left i =>
      induction j using Fin.addCases with
      | left j =>
        exact congrArg L (Fin.castSucc_injective _
          (hp.injective (by simpa only [r, Fin.append_left] using hij)))
      | right j => exact (hcross i j (by simpa only [← hL, ← hR] using hij)).elim
    | right i =>
      induction j using Fin.addCases with
      | left j => exact (hcross j i (by simpa only [← hL, ← hR] using hij.symm)).elim
      | right j =>
        exact congrArg R (Fin.castSucc_injective _
          (hq.injective (by simpa only [r, Fin.append_right] using hij)))
  have hcross_edges (i : Fin (n₁ + 2)) (j : Fin (n₂ + 2)) {z : ℂ}
      (hz : z ∈ r.edgeSet ℝ (L i) ∩ r.edgeSet ℝ (R j)) :
      z ∈ ({r (L i), r (finRotate _ (L i))} : Set ℂ) ∩
        {r (R j), r (finRotate _ (R j))} := by
    have hzp : z ∈ p.edgeSet ℝ i.castSucc := hLe i ▸ hz.1
    have hzq : z ∈ q.edgeSet ℝ j.castSucc := hRe j ▸ hz.2
    have hzs : z ∈ segment ℝ a b := by
      rw [← hinter]
      exact ⟨mem_iUnion.mpr ⟨_, hzp⟩, mem_iUnion.mpr ⟨_, hzq⟩⟩
    have hpends := (hp.simple i.castSucc (Fin.last (n₁ + 2)) (Fin.castSucc_ne_last i)
      ⟨hzp, hpseam ▸ hzs⟩).1
    have hqends := (hq.simple j.castSucc (Fin.last (n₂ + 2)) (Fin.castSucc_ne_last j)
      ⟨hzq, hqseam ▸ hzs⟩).1
    simpa only [hL, hR, hLs, hRs, hpnext, hqnext, mem_inter_iff] using And.intro hpends hqends
  have hendnot {z : ℂ} (hz : z ∈ ({a, b} : Set ℂ)) : z ∉ openSegment ℝ a b := by
    rcases hz with rfl | hz
    · exact fun hh ↦ hab (left_mem_openSegment_iff.mp hh)
    · subst z
      exact fun hh ↦ hab (right_mem_openSegment_iff.mp hh)
  have hpavoid (i : Fin (n₁ + 2)) {z : ℂ} (hz : z ∈ p.edgeSet ℝ i.castSucc) :
      z ∉ openSegment ℝ a b := by
    intro hs
    have he := (hp.simple i.castSucc (Fin.last (n₁ + 2)) (Fin.castSucc_ne_last i)
      ⟨hz, hpseam ▸ openSegment_subset_segment ℝ a b hs⟩).2
    have hzends : z ∈ ({a, b} : Set ℂ) := by
      simpa only [finRotate_last, hplast, hp0, pair_comm b a] using he
    exact hendnot hzends hs
  have hqavoid (i : Fin (n₂ + 2)) {z : ℂ} (hz : z ∈ q.edgeSet ℝ i.castSucc) :
      z ∉ openSegment ℝ a b := by
    intro hs
    have he := (hq.simple i.castSucc (Fin.last (n₂ + 2)) (Fin.castSucc_ne_last i)
      ⟨hz, hqseam ▸ openSegment_subset_segment ℝ a b hs⟩).2
    have hzends : z ∈ ({a, b} : Set ℂ) := by
      simpa only [finRotate_last, hqlast, hq0] using he
    exact hendnot hzends hs
  have hra : a ∈ r.boundary ℝ := by
    have hv : r (L 0) = a := by simp only [hL, Fin.castSucc_zero, hp0]
    exact hv ▸ mem_iUnion.mpr ⟨L 0, left_mem_affineSegment ℝ _ _⟩
  have hrb : b ∈ r.boundary ℝ := by
    have hv : r (R 0) = b := by simp only [hR, Fin.castSucc_zero, hq0]
    exact hv ▸ mem_iUnion.mpr ⟨R 0, left_mem_affineSegment ℝ _ _⟩
  refine ⟨r, ⟨hrij, ?_⟩, ?_⟩
  · intro i j hij z hz
    induction i using Fin.addCases with
    | left i =>
      induction j using Fin.addCases with
      | left j =>
        have hne : i.castSucc ≠ j.castSucc := fun he ↦
          hij (congrArg L (Fin.castSucc_injective _ he))
        have he := hp.simple i.castSucc j.castSucc hne
          ⟨hLe i ▸ hz.1, hLe j ▸ hz.2⟩
        simpa only [hpnext, ← hL, ← hLs] using he
      | right j => exact hcross_edges i j hz
    | right i =>
      induction j using Fin.addCases with
      | left j => exact (hcross_edges j i ⟨hz.2, hz.1⟩).symm
      | right j =>
        have hne : i.castSucc ≠ j.castSucc := fun he ↦
          hij (congrArg R (Fin.castSucc_injective _ he))
        have he := hq.simple i.castSucc j.castSucc hne
          ⟨hRe i ▸ hz.1, hRe j ▸ hz.2⟩
        simpa only [hqnext, ← hR, ← hRs] using he
  · apply subset_antisymm
    · intro z hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      induction i using Fin.addCases with
      | left i =>
        have hpz : z ∈ p.edgeSet ℝ i.castSucc := hLe i ▸ hi
        exact ⟨Or.inl (mem_iUnion.mpr ⟨_, hpz⟩), hpavoid i hpz⟩
      | right i =>
        have hqz : z ∈ q.edgeSet ℝ i.castSucc := hRe i ▸ hi
        exact ⟨Or.inr (mem_iUnion.mpr ⟨_, hqz⟩), hqavoid i hqz⟩
    · rintro z ⟨hz | hz, hnot⟩
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hz
        by_cases hil : i = Fin.last (n₁ + 2)
        · subst i
          rw [hpseam, ← insert_endpoints_openSegment] at hi
          rcases hi with rfl | rfl | hi
          · exact hra
          · exact hrb
          · exact (hnot hi).elim
        · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hil
          exact mem_iUnion.mpr ⟨L j, hLe j ▸ hi⟩
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hz
        by_cases hil : i = Fin.last (n₂ + 2)
        · subst i
          rw [hqseam, ← insert_endpoints_openSegment] at hi
          rcases hi with rfl | rfl | hi
          · exact hra
          · exact hrb
          · exact (hnot hi).elim
        · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hil
          exact mem_iUnion.mpr ⟨R j, hRe j ▸ hi⟩

end HolomorphicAnosov
