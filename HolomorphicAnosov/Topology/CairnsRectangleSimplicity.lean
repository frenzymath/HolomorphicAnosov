import HolomorphicAnosov.Topology.CairnsRectangleAdjacentIntersections
import Mathlib.Tactic
open Set
namespace HolomorphicAnosov
/-- Distinct rectangle edges intersect only at vertices shared by both edges. -/
theorem cairns_rectangle_edge_intersection_subset (L R B T : ℝ) (hLR : L < R) (hBT : B < T) :
    ∀ i j : Fin 4, i ≠ j →
      (cairnsRectanglePolygon L R B T hLR hBT).edgeSet ℝ i ∩
          (cairnsRectanglePolygon L R B T hLR hBT).edgeSet ℝ j ⊆
        (cairnsRectanglePolygon L R B T hLR hBT).vertices ''
          ({i, finRotate 4 i} ∩ {j, finRotate 4 j}) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals try contradiction
  all_goals norm_num at *
  · rw [cairns_rectangle_lower_right_intersection L R B T hLR hBT]
    intro z hz
    have hz' := Set.mem_singleton_iff.mp hz
    subst z
    refine ⟨(1 : Fin 4), ?_, ?_⟩
    · norm_num
    · rfl
  · rw [cairns_rectangle_opposite_horizontal_disjoint L R B T hLR hBT]
    exact Set.empty_subset _
  · rw [Set.inter_comm]
    rw [cairns_rectangle_lower_left_intersection L R B T hLR hBT]
    intro z hz
    have hz' := Set.mem_singleton_iff.mp hz
    subst z
    refine ⟨(0 : Fin 4), ?_, ?_⟩
    · norm_num
    · rfl
  · rw [Set.inter_comm]
    rw [cairns_rectangle_lower_right_intersection L R B T hLR hBT]
    intro z hz
    have hz' := Set.mem_singleton_iff.mp hz
    subst z
    refine ⟨(1 : Fin 4), ?_, ?_⟩
    · norm_num
    · rfl
  · rw [cairns_rectangle_upper_right_intersection L R B T hLR hBT]
    intro z hz
    have hz' := Set.mem_singleton_iff.mp hz
    subst z
    refine ⟨(2 : Fin 4), ?_, ?_⟩
    · norm_num
    · rfl
  · rw [cairns_rectangle_opposite_vertical_disjoint L R B T hLR hBT]
    exact Set.empty_subset _
  · rw [Set.inter_comm]
    rw [cairns_rectangle_opposite_horizontal_disjoint L R B T hLR hBT]
    exact Set.empty_subset _
  · rw [Set.inter_comm]
    rw [cairns_rectangle_upper_right_intersection L R B T hLR hBT]
    intro z hz
    have hz' := Set.mem_singleton_iff.mp hz
    subst z
    refine ⟨(2 : Fin 4), ?_, ?_⟩
    · norm_num
    · rfl
  · rw [cairns_rectangle_upper_left_intersection L R B T hLR hBT]
    intro z hz
    have hz' := Set.mem_singleton_iff.mp hz
    subst z
    refine ⟨(3 : Fin 4), ?_, ?_⟩
    · norm_num
    · rfl
  · rw [cairns_rectangle_lower_left_intersection L R B T hLR hBT]
    intro z hz
    have hz' := Set.mem_singleton_iff.mp hz
    subst z
    refine ⟨(0 : Fin 4), ?_, ?_⟩
    · norm_num
    · rfl
  · rw [Set.inter_comm]
    rw [cairns_rectangle_opposite_vertical_disjoint L R B T hLR hBT]
    exact Set.empty_subset _
  · rw [Set.inter_comm]
    rw [cairns_rectangle_upper_left_intersection L R B T hLR hBT]
    intro z hz
    have hz' := Set.mem_singleton_iff.mp hz
    subst z
    refine ⟨(3 : Fin 4), ?_, ?_⟩
    · norm_num
    · rfl

end HolomorphicAnosov
