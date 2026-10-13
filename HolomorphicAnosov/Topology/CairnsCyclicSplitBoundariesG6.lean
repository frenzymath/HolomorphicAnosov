import HolomorphicAnosov.Topology.PolygonEdgeIntersection
import Mathlib.Analysis.Complex.Circle
import Mathlib.Tactic

open Set Fin.NatCast
namespace HolomorphicAnosov

/-- The boundary of a cyclic subpolygon consists of its consecutive old edges and its closing
chord. This is the finite edge bookkeeping in Cairns (1951), Theorem 2.1. -/
theorem cairns_cyclic_arc_boundary_g6 {n : ℕ} (p : Polygon ℂ (n + 1))
    (i : Fin (n + 1)) (k : ℕ) :
    (Polygon.mk (fun r : Fin (k + 1) ↦ p ((finRotate (n + 1))^[r.val] i))).boundary ℝ =
      (⋃ r : Fin k, p.edgeSet ℝ ((finRotate (n + 1))^[r.val] i)) ∪
        segment ℝ (p ((finRotate (n + 1))^[k] i)) (p i) := by
  let q : Polygon ℂ (k + 1) := ⟨fun r ↦ p ((finRotate (n + 1))^[r.val] i)⟩
  have hedge (r : Fin k) : q.edgeSet ℝ r.castSucc =
      p.edgeSet ℝ ((finRotate (n + 1))^[r.val] i) := by
    simp only [Polygon.edgeSet, q]
    congr 2
    rw [coe_finRotate_of_ne_last (Fin.castSucc_ne_last r), Fin.val_castSucc,
      Function.iterate_succ_apply']
  have hlast : q.edgeSet ℝ (Fin.last k) =
      segment ℝ (p ((finRotate (n + 1))^[k] i)) (p i) := by
    simp only [Polygon.edgeSet, finRotate_last, q, Fin.val_last,
      Fin.val_zero, Function.iterate_zero_apply, affineSegment_eq_segment]
  change q.boundary ℝ = _
  rw [Polygon.boundary, ← hlast]
  apply subset_antisymm
  · apply iUnion_subset
    intro r
    refine Fin.lastCases ?_ (fun r ↦ ?_) r
    · exact subset_union_right
    · rw [hedge]
      intro z hz
      exact Or.inl (mem_iUnion.mpr ⟨r, hz⟩)
  · apply union_subset
    · apply iUnion_subset
      intro r
      rw [← hedge]
      exact subset_iUnion _ r.castSucc
    · exact subset_iUnion _ (Fin.last k)

/-- Cutting a simple polygon along a boundary-disjoint diagonal gives two cycles whose union
is the old boundary together with the chord, and whose intersection is exactly that chord.
Source: Cairns (1951), Theorem 2.1, the two cyclic arcs in the induction step. -/
theorem cairns_cyclic_split_boundaries_g6 {n : ℕ} (p : Polygon ℂ (n + 1))
    (_hinj : Function.Injective p.vertices)
    (hsimple : ∀ u v : Fin (n + 1), u ≠ v →
      p.edgeSet ℝ u ∩ p.edgeSet ℝ v ⊆
        p.vertices '' ({u, finRotate (n + 1) u} ∩ {v, finRotate (n + 1) v}))
    (i j : Fin (n + 1)) (a b : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : a + b = n + 1)
    (hj : j = (finRotate (n + 1))^[a] i)
    (hdiag : Disjoint (openSegment ℝ (p i) (p j)) (p.boundary ℝ)) :
    let A := Polygon.mk (fun r : Fin (a + 1) ↦ p ((finRotate (n + 1))^[r.val] i))
    let B := Polygon.mk (fun r : Fin (b + 1) ↦ p ((finRotate (n + 1))^[r.val] j))
    A.boundary ℝ ∩ B.boundary ℝ = segment ℝ (p i) (p j) ∧
      (A.boundary ℝ ∪ B.boundary ℝ) \ openSegment ℝ (p i) (p j) = p.boundary ℝ := by
  classical
  intro A B
  have hiter (m : ℕ) (hm : m < n + 1) (r : Fin (n + 1)) :
      (finRotate (n + 1))^[m] r = r + (⟨m, hm⟩ : Fin (n + 1)) :=
    (congrFun (finCycle_eq_finRotate_iterate (k := ⟨m, hm⟩)) r).symm
  have : NeZero (n + 1) := ⟨by omega⟩
  have hiterAll (m : ℕ) (r : Fin (n + 1)) :
      (finRotate (n + 1))^[m] r = r + (m : Fin (n + 1)) := by
    induction m with
    | zero => simp
    | succ m ih => simp only [Function.iterate_succ_apply', ih, finRotate_apply,
        Nat.cast_add, Nat.cast_one, add_assoc]
  have hreturn : (finRotate (n + 1))^[b] j = i := by
    rw [hiter b (by omega), hj, hiter a (by omega), add_assoc]
    have hzero : (⟨a, by omega⟩ : Fin (n + 1)) + ⟨b, by omega⟩ = 0 := by
      apply Fin.ext
      change (a + b) % (n + 1) = 0
      rw [hab, Nat.mod_self]
    rw [hzero, add_zero]
  have hedgeB (r : Fin b) : (finRotate (n + 1))^[r.val] j =
      (finRotate (n + 1))^[a + r.val] i := by
    rw [hj, ← Function.iterate_add_apply, Nat.add_comm r.val a]
  let EA := ⋃ r : Fin a, p.edgeSet ℝ ((finRotate (n + 1))^[r.val] i)
  let EB := ⋃ r : Fin b, p.edgeSet ℝ ((finRotate (n + 1))^[a + r.val] i)
  let D := segment ℝ (p i) (p j)
  have hA : A.boundary ℝ = EA ∪ D := by
    rw [cairns_cyclic_arc_boundary_g6, ← hj, segment_symm]
  have hB : B.boundary ℝ = EB ∪ D := by
    rw [cairns_cyclic_arc_boundary_g6, hreturn]
    simp only [hedgeB, EB, D]
  have hcover : EA ∪ EB = p.boundary ℝ := by
    apply subset_antisymm
    · apply union_subset <;> apply iUnion_subset <;> intro r <;>
        exact subset_iUnion (p.edgeSet ℝ) _
    · apply iUnion_subset
      intro k
      let d : Fin (n + 1) := k - i
      have hidx : (finRotate (n + 1))^[d.val] i = k := by
        rw [hiter d.val d.isLt]
        exact add_sub_cancel _ _
      by_cases hd : d.val < a
      · intro z hz
        exact Or.inl (mem_iUnion.mpr ⟨⟨d.val, hd⟩, hidx ▸ hz⟩)
      · have hdb : d.val - a < b := by omega
        intro z hz
        apply Or.inr
        apply mem_iUnion.mpr
        refine ⟨⟨d.val - a, hdb⟩, ?_⟩
        have hsum : a + (d.val - a) = d.val := by omega
        simpa only [hsum, hidx] using hz
  have hinter : EA ∩ EB ⊆ D := by
    intro z hz
    obtain ⟨r, hr⟩ := mem_iUnion.mp hz.1
    obtain ⟨s, hs⟩ := mem_iUnion.mp hz.2
    have hne : (finRotate (n + 1))^[r.val] i ≠
        (finRotate (n + 1))^[a + s.val] i := by
      rw [hiter r.val (by omega), hiter (a + s.val) (by omega)]
      intro h
      have hh := congrArg Fin.val (add_left_cancel h)
      dsimp at hh
      omega
    obtain ⟨k, ⟨hkr, hks⟩, hkz⟩ := hsimple _ _ hne ⟨hr, hs⟩
    simp only [mem_insert_iff, mem_singleton_iff] at hkr hks
    have hendpoint : k = i ∨ k = j := by
      have har : r.val < a := r.isLt
      have hbs : s.val < b := s.isLt
      have hmodr : r.val % (n + 1) = r.val := Nat.mod_eq_of_lt (by omega)
      have hmodr1 : (r.val + 1) % (n + 1) = r.val + 1 := Nat.mod_eq_of_lt (by omega)
      have hmods : (a + s.val) % (n + 1) = a + s.val := Nat.mod_eq_of_lt (by omega)
      have hmods1 : (a + s.val + 1) % (n + 1) = 0 ∨
          (a + s.val + 1) % (n + 1) = a + s.val + 1 := by
        by_cases h : a + s.val + 1 = n + 1
        · exact Or.inl (by rw [h, Nat.mod_self])
        · exact Or.inr (Nat.mod_eq_of_lt (by omega))
      rcases hkr with rfl | rfl <;> rcases hks with h | h
      · exact (hne h).elim
      · rw [← Function.iterate_succ_apply' (finRotate (n + 1)), hiterAll, hiterAll] at h
        have hv := congrArg Fin.val (add_left_cancel h)
        simp only [Fin.val_natCast, Nat.succ_eq_add_one, hmodr] at hv
        have hr0 : r.val = 0 := by omega
        left
        simp [hr0]
      · rw [← Function.iterate_succ_apply' (finRotate (n + 1)), hiterAll, hiterAll] at h
        have hv := congrArg Fin.val (add_left_cancel h)
        simp only [Fin.val_natCast, Nat.succ_eq_add_one, hmodr1, hmods] at hv
        have hra : r.val + 1 = a := by omega
        right
        rw [← Function.iterate_succ_apply' (finRotate (n + 1)), Nat.succ_eq_add_one, hra, ← hj]
      · rw [← Function.iterate_succ_apply' (finRotate (n + 1)), ← Function.iterate_succ_apply' (finRotate (n + 1)),
          hiterAll, hiterAll] at h
        have hv := congrArg Fin.val (add_left_cancel h)
        simp only [Fin.val_natCast, Nat.succ_eq_add_one, hmodr1] at hv
        omega
    rcases hendpoint with rfl | rfl
    · exact hkz ▸ left_mem_segment ℝ _ _
    · exact hkz ▸ right_mem_segment ℝ _ _
  constructor
  · rw [hA, hB]
    apply subset_antisymm
    · intro z hz
      rcases hz.1 with hzA | hzD
      · rcases hz.2 with hzB | hzD
        · exact hinter ⟨hzA, hzB⟩
        · exact hzD
      · exact hzD
    · intro z hz
      exact ⟨Or.inr hz, Or.inr hz⟩
  · rw [hA, hB]
    have hu : (EA ∪ D) ∪ (EB ∪ D) = p.boundary ℝ ∪ D := by
      rw [← hcover]
      ext z
      simp only [mem_union]
      tauto
    rw [hu]
    apply subset_antisymm
    · rintro z ⟨hz, hn⟩
      rcases hz with hz | hz
      · exact hz
      · change z ∈ segment ℝ (p i) (p j) at hz
        rw [← insert_endpoints_openSegment] at hz
        rcases hz with hz | hz | hz
        · exact hz ▸ mem_iUnion.mpr ⟨i, left_mem_affineSegment ℝ _ _⟩
        · exact hz ▸ mem_iUnion.mpr ⟨j, left_mem_affineSegment ℝ _ _⟩
        · exact (hn hz).elim
    · intro z hz
      exact ⟨Or.inl hz, fun hd ↦ disjoint_left.mp hdiag hd hz⟩

end HolomorphicAnosov
