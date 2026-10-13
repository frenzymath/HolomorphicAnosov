import HolomorphicAnosov.Topology.CairnsRectangleEdgeCertificate
import HolomorphicAnosov.Topology.CairnsExtremeContactNotchIntersections
import Mathlib.Tactic

open Set

namespace HolomorphicAnosov

/-- The lower-right adjacent rectangle edges meet exactly at the lower-right corner. -/
theorem cairns_rectangle_lower_right_intersection
    (L R B T : ℝ) (hLR : L < R) (hBT : B < T) :
    (cairnsRectanglePolygon L R B T hLR hBT).edgeSet ℝ 0 ∩
      (cairnsRectanglePolygon L R B T hLR hBT).edgeSet ℝ 1 =
      {R + B * Complex.I} := by
  simp only [Polygon.edgeSet, affineSegment_eq_segment, cairnsRectanglePolygon]
  have h := cairns_rectangle_adjacent_edges_meet_at_corner
    (L + B * Complex.I) (R - L) (T - B) (by linarith) (by linarith)
  convert h using 1 <;> simp <;> ring

/-- The upper-right adjacent rectangle edges meet exactly at the upper-right corner. -/
theorem cairns_rectangle_upper_right_intersection
    (L R B T : ℝ) (hLR : L < R) (hBT : B < T) :
    (cairnsRectanglePolygon L R B T hLR hBT).edgeSet ℝ 1 ∩
      (cairnsRectanglePolygon L R B T hLR hBT).edgeSet ℝ 2 =
      {R + T * Complex.I} := by
  simp only [Polygon.edgeSet, affineSegment_eq_segment, cairnsRectanglePolygon]
  have h := cairns_rectangle_vertical_then_horizontal_edges_meet_at_corner
    (R + B * Complex.I) (L - R) (T - B) (by linarith) (by linarith)
  convert h using 1 <;> simp <;> ring

/-- The upper-left adjacent rectangle edges meet exactly at the upper-left corner. -/
theorem cairns_rectangle_upper_left_intersection
    (L R B T : ℝ) (hLR : L < R) (hBT : B < T) :
    (cairnsRectanglePolygon L R B T hLR hBT).edgeSet ℝ 2 ∩
      (cairnsRectanglePolygon L R B T hLR hBT).edgeSet ℝ 3 =
      {L + T * Complex.I} := by
  simp only [Polygon.edgeSet, affineSegment_eq_segment, cairnsRectanglePolygon]
  have h := cairns_rectangle_adjacent_edges_meet_at_corner
    (R + T * Complex.I) (L - R) (B - T) (by linarith) (by linarith)
  convert h using 1 <;> simp <;> ring

/-- The lower-left adjacent rectangle edges meet exactly at the lower-left corner. -/
theorem cairns_rectangle_lower_left_intersection
    (L R B T : ℝ) (hLR : L < R) (hBT : B < T) :
    (cairnsRectanglePolygon L R B T hLR hBT).edgeSet ℝ 3 ∩
      (cairnsRectanglePolygon L R B T hLR hBT).edgeSet ℝ 0 =
      {L + B * Complex.I} := by
  simp only [Polygon.edgeSet, affineSegment_eq_segment, cairnsRectanglePolygon]
  have h := cairns_rectangle_vertical_then_horizontal_edges_meet_at_corner
    (L + T * Complex.I) (R - L) (B - T) (by linarith) (by linarith)
  convert h using 1 <;> simp <;> ring

end HolomorphicAnosov
