import HolomorphicAnosov.Topology.BoundaryCycleCircleG9
import Mathlib.Geometry.Polygon.Basic
import Mathlib.Analysis.Convex.PathConnected

open Set
namespace HolomorphicAnosov

/-- A finite polygon with injective vertices and only common-endpoint edge intersections
parametrizes an embedded circle. Cairns (1951), Theorem 2.1: concatenate its consecutive
nonclosing edges into a simple arc, then join the closing edge and identify the two endpoints. -/
theorem cairns_polygon_boundary_circle_g6 {n : ℕ} (p : Polygon ℂ n) (hn : 3 ≤ n)
    (hp : Function.Injective p.vertices)
    (hs : ∀ i j : Fin n, i ≠ j →
      p.edgeSet ℝ i ∩ p.edgeSet ℝ j ⊆
        p.vertices '' ({i, finRotate n i} ∩ {j, finRotate n j})) :
    ∃ γ : Circle → ℂ, _root_.Topology.IsEmbedding γ ∧ range γ = p.boundary ℝ := by
  classical
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hrot (k : Fin (n + 3)) (hk : k.val < n + 2) :
      (finRotate (n + 3) k).val = k.val + 1 :=
    coe_finRotate_of_ne_last (by intro h; have := congrArg Fin.val h; simp at this; omega)
  have chain (k : ℕ) (hk0 : 0 < k) (hkN : k < n + 3) :
      ∃ α : Path (p 0) (p ⟨k, hkN⟩), Function.Injective α ∧
        range α = ⋃ r : Fin k, p.edgeSet ℝ ⟨r.val, by omega⟩ := by
    induction k with
    | zero => omega
    | succ k ih =>
      by_cases hk : k = 0
      · subst k
        refine ⟨Path.segment (p 0) (p ⟨1, hkN⟩),
          Path.segment_injective_of_ne (hp.ne (by intro h; have := congrArg Fin.val h; simp at this)), ?_⟩
        rw [Path.range_segment]
        have he : p.edgeSet ℝ (0 : Fin (n + 3)) = segment ℝ (p 0) (p ⟨1, hkN⟩) := by
          rw [Polygon.edgeSet, affineSegment_eq_segment]
          congr 1
        ext z
        simp only [mem_iUnion]
        constructor
        · intro hz
          exact ⟨0, he ▸ hz⟩
        · rintro ⟨r, hr⟩
          have hr0 : r.val = 0 := by omega
          have he0 : (⟨r.val, by omega⟩ : Fin (n + 3)) = 0 := Fin.ext (by simp)
          simpa only [he0, he] using hr
      · obtain ⟨α, hα, hαrange⟩ := ih (by omega) (by omega)
        let β : Path (p ⟨k, by omega⟩) (p ⟨k + 1, hkN⟩) := Path.segment _ _
        have hβ : Function.Injective β := Path.segment_injective_of_ne (hp.ne (by
          intro h; have := congrArg Fin.val h; simp only at this; omega))
        have hβrange : range β = p.edgeSet ℝ ⟨k, by omega⟩ := by
          rw [show range β = _ from Path.range_segment _ _, Polygon.edgeSet,
            affineSegment_eq_segment]
          congr 1
          apply congrArg p
          apply Fin.ext
          exact (hrot ⟨k, by omega⟩ (by change k < n + 2; omega)).symm
        have hcross (s t : unitInterval) (h : α s = β t) : s = 1 ∧ t = 0 := by
          have hm : α s ∈ ⋃ r : Fin k, p.edgeSet ℝ ⟨r.val, by omega⟩ :=
            hαrange ▸ mem_range_self s
          obtain ⟨r, hr⟩ := mem_iUnion.mp hm
          have ht : α s ∈ p.edgeSet ℝ ⟨k, by omega⟩ :=
            h.symm ▸ (hβrange ▸ mem_range_self t)
          have hrk : (⟨r.val, by omega⟩ : Fin (n + 3)) ≠ ⟨k, by omega⟩ := by
            intro hh; have := congrArg Fin.val hh; simp only at this; omega
          obtain ⟨l, ⟨hlr, hlk⟩, hl⟩ := hs _ _ hrk ⟨hr, ht⟩
          have hlk' : l = (⟨k, by omega⟩ : Fin (n + 3)) := by
            simp only [mem_insert_iff, mem_singleton_iff] at hlr hlk
            rcases hlk with h | h
            · exact h
            · have hv := congrArg Fin.val h
              rw [hrot ⟨k, by omega⟩ (by change k < n + 2; omega)] at hv
              change l.val = k + 1 at hv
              rcases hlr with hr | hr
              · have hv' := congrArg Fin.val hr
                simp only at hv'
                omega
              · have hv' := congrArg Fin.val hr
                rw [hrot ⟨r.val, by omega⟩ (by change r.val < n + 2; omega)] at hv'
                change l.val = r.val + 1 at hv'
                omega
          have he : α s = p ⟨k, by omega⟩ := hl.symm.trans (congrArg p hlk')
          refine ⟨hα (he.trans α.target.symm), hβ ?_⟩
          exact h.symm.trans (he.trans β.source.symm)
        refine ⟨α.trans β,
          Topology.GallierXu.path_trans_injective_g9 α β hα hβ hcross, ?_⟩
        rw [Path.trans_range, hαrange, hβrange]
        ext z
        simp only [mem_union, mem_iUnion]
        constructor
        · rintro (⟨r, hr⟩ | hr)
          · exact ⟨r.castSucc, hr⟩
          · exact ⟨Fin.last k, hr⟩
        · rintro ⟨r, hr⟩
          cases r using Fin.lastCases with
          | last => exact Or.inr hr
          | cast r => exact Or.inl ⟨r, hr⟩
  obtain ⟨α, hα, hαrange⟩ := chain (n + 2) (by omega) (by omega)
  let β : Path (p 0) (p (Fin.last (n + 2))) := Path.segment _ _
  have hβ : Function.Injective β := Path.segment_injective_of_ne (hp.ne (by
    intro h; have := congrArg Fin.val h; simp only [Fin.val_zero, Fin.val_last] at this; omega))
  have hβrange : range β = p.edgeSet ℝ (Fin.last (n + 2)) := by
    rw [show range β = _ from Path.range_segment _ _, Polygon.edgeSet, finRotate_last,
      affineSegment_eq_segment, segment_symm]
  have hcross (s t : unitInterval) (h : α s = β t) :
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    have hm := hαrange ▸ mem_range_self s
    obtain ⟨r, hr⟩ := mem_iUnion.mp hm
    have ht : α s ∈ p.edgeSet ℝ (Fin.last (n + 2)) :=
      h.symm ▸ (hβrange ▸ mem_range_self t)
    have hrk : (⟨r.val, by omega⟩ : Fin (n + 3)) ≠ Fin.last (n + 2) := by
      intro hh; have := congrArg Fin.val hh; simp only [Fin.val_last] at this; omega
    obtain ⟨l, ⟨_, hlk⟩, hl⟩ := hs _ _ hrk ⟨hr, ht⟩
    simp only [finRotate_last, mem_insert_iff, mem_singleton_iff] at hlk
    rcases hlk with rfl | rfl
    · exact Or.inr ⟨hα (hl.symm.trans α.target.symm),
        hβ (h.symm.trans (hl.symm.trans β.target.symm))⟩
    · exact Or.inl ⟨hα (hl.symm.trans α.source.symm),
        hβ (h.symm.trans (hl.symm.trans β.source.symm))⟩
  obtain ⟨γ, hγ, hrange⟩ := twoArcs_circle_embedding α β α.continuous β.continuous hα hβ
    (α.source.trans β.source.symm) (α.target.trans β.target.symm) hcross
  refine ⟨γ, hγ, hrange.trans ?_⟩
  rw [hαrange, hβrange]
  ext z
  simp only [mem_union, mem_iUnion, Polygon.boundary]
  constructor
  · rintro (⟨r, hr⟩ | hr)
    · exact ⟨⟨r.val, by omega⟩, hr⟩
    · exact ⟨Fin.last (n + 2), hr⟩
  · rintro ⟨r, hr⟩
    cases r using Fin.lastCases with
    | last => exact Or.inr hr
    | cast r => exact Or.inl ⟨r, hr⟩

end HolomorphicAnosov
