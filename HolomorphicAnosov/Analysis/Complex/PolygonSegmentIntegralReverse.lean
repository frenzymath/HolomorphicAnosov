import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-!
# Reversal of a polygonal segment integral

Source: Rudin, Real and Complex Analysis, third edition (1987), Definition10.8
p.201, equation (4), and §10.9(b), p.202, equation (4). Conway VIII.1.1 p.196
uses this reversal identity to cancel shared square sides.
DAG node: `analysis.polygon_segment_integral_reverse_g19`.
-/

namespace HolomorphicAnosov.Analysis.Complex

/-- Reversing a segment negates its oriented affine-parameter integral.

Source: Rudin Definition10.8 p.201, equation (4), substitutes s=1−t; §10.9(b)
p.202, equation (4), identifies the tangent factor b−a. The affine-map identity
lineMap(a,b,1−t)=lineMap(b,a,t) and the native interval change-of-variable theorem
show the unoriented parameter integrals agree. The tangent factors are negatives.
Mathlib's substitution identity also covers its total integral on nonintegrable
functions, so the formula needs no continuity assumption. For coincident endpoints
both oriented integrals are zero. -/
theorem polygon_segment_integral_reverse (f : ℂ → ℂ) (a b : ℂ) :
    (a - b) * (∫ t in (0 : ℝ)..1, f (AffineMap.lineMap b a t)) =
      -((b - a) * (∫ t in (0 : ℝ)..1, f (AffineMap.lineMap a b t))) := by
  have hi : (∫ t in (0 : ℝ)..1, f (AffineMap.lineMap b a t)) =
      ∫ t in (0 : ℝ)..1, f (AffineMap.lineMap a b t) := by
    calc
      _ = ∫ t in (0 : ℝ)..1, f (AffineMap.lineMap a b (1 - t)) := by
        simp only [AffineMap.lineMap_apply_one_sub]
      _ = _ := by
        simpa using intervalIntegral.integral_comp_sub_left
          (fun t : ℝ ↦ f (AffineMap.lineMap a b t)) (a := 0) (b := 1) 1
  rw [hi]
  ring

end HolomorphicAnosov.Analysis.Complex
