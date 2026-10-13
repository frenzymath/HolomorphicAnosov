import Mathlib.Analysis.Complex.Circle
import Mathlib.Geometry.Polygon.Basic
import Mathlib.Tactic

namespace HolomorphicAnosov

/-- The four-corner rectangle carrier used before the two Cairns notch replacements. -/
def cairnsRectanglePolygon (L R B T : ℝ) (_hLR : L < R) (_hBT : B < T) : Polygon ℂ 4 :=
  ⟨![L + B * Complex.I, R + B * Complex.I, R + T * Complex.I, L + T * Complex.I]⟩

/-- The rectangle carrier has distinct cyclic vertices. -/
theorem cairns_rectangle_polygon_vertices_injective
    (L R B T : ℝ) (hLR : L < R) (hBT : B < T) :
    Function.Injective (cairnsRectanglePolygon L R B T hLR hBT).vertices := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [cairnsRectanglePolygon, Complex.ext_iff] <;> linarith

/-- Every rectangle edge is nondegenerate. -/
theorem cairns_rectangle_polygon_nondegenerate_edges
    (L R B T : ℝ) (hLR : L < R) (hBT : B < T) :
    (cairnsRectanglePolygon L R B T hLR hBT).HasNondegenerateEdges := by
  intro i
  fin_cases i <;> simp [cairnsRectanglePolygon, Complex.ext_iff] <;> linarith

end HolomorphicAnosov
