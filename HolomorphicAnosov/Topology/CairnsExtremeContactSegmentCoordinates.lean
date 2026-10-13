import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Complex.Circle

open Set

namespace HolomorphicAnosov

/-- Every point of an affine segment whose endpoints share a real coordinate has that coordinate. -/
theorem cairns_segment_re_eq_of_endpoints
    (A B z : ℂ) (x : ℝ) (hz : z ∈ segment ℝ A B)
    (hA : A.re = x) (hB : B.re = x) : z.re = x := by
  rw [segment_eq_image_lineMap ℝ A B] at hz
  obtain ⟨t, ht, hzt⟩ := hz
  rw [← hzt]
  have hre : (AffineMap.lineMap A B t).re = t * (B.re - A.re) + A.re := by
    simp [AffineMap.lineMap_apply, vsub_eq_sub, add_comm]
  rw [hre, hA, hB]
  ring

/-- Every point of an affine segment whose endpoints share an imaginary coordinate has that coordinate. -/
theorem cairns_segment_im_eq_of_endpoints
    (A B z : ℂ) (y : ℝ) (hz : z ∈ segment ℝ A B)
    (hA : A.im = y) (hB : B.im = y) : z.im = y := by
  rw [segment_eq_image_lineMap ℝ A B] at hz
  obtain ⟨t, ht, hzt⟩ := hz
  rw [← hzt]
  have him : (AffineMap.lineMap A B t).im = t * (B.im - A.im) + A.im := by
    simp [AffineMap.lineMap_apply, vsub_eq_sub, add_comm]
  rw [him, hA, hB]
  ring

end HolomorphicAnosov
