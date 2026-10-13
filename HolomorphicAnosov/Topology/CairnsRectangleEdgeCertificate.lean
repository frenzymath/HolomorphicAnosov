import HolomorphicAnosov.Topology.CairnsRectanglePolygonData
import HolomorphicAnosov.Topology.CairnsRectangleEdgeIntersections
import Mathlib.Analysis.Convex.Segment

open Set

namespace HolomorphicAnosov

/-- Opposite horizontal rectangle edges are disjoint. -/
theorem cairns_rectangle_opposite_horizontal_disjoint
    (L R B T : ℝ) (hLR : L < R) (hBT : B < T) :
    (cairnsRectanglePolygon L R B T hLR hBT).edgeSet ℝ 0 ∩
      (cairnsRectanglePolygon L R B T hLR hBT).edgeSet ℝ 2 = ∅ := by
  apply Set.disjoint_iff_inter_eq_empty.mp
  simp only [Polygon.edgeSet, affineSegment_eq_segment, cairnsRectanglePolygon]
  apply cairns_horizontal_segments_disjoint
  · simp
  · simp
  · simp
    exact ne_of_lt hBT

/-- Opposite vertical rectangle edges are disjoint. -/
theorem cairns_rectangle_opposite_vertical_disjoint
    (L R B T : ℝ) (hLR : L < R) (hBT : B < T) :
    (cairnsRectanglePolygon L R B T hLR hBT).edgeSet ℝ 1 ∩
      (cairnsRectanglePolygon L R B T hLR hBT).edgeSet ℝ 3 = ∅ := by
  apply Set.disjoint_iff_inter_eq_empty.mp
  simp only [Polygon.edgeSet, affineSegment_eq_segment, cairnsRectanglePolygon]
  apply cairns_vertical_segments_disjoint
  · simp
  · simp
  · simp
    exact ne_of_gt hLR

end HolomorphicAnosov
