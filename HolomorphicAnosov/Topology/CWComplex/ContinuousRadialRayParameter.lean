import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace HolomorphicAnosov

/-- Continuity off the pole of the quadratic-root radial parameter used
in Hatcher Theorem 4.8, p.349. Inner products, norms, square roots and
arithmetic are continuous; the denominator is nonzero exactly off p.
No disk membership or interior-pole hypothesis is needed for continuity.
-/
theorem continuous_radial_ray_parameter
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : E) : Continuous (fun z : {z : E // z ≠ p} ↦
      (-inner ℝ p (z.val-p) + Real.sqrt ((inner ℝ p (z.val-p)) ^ 2 +
        (1 - ‖p‖ ^ 2) * ‖z.val-p‖ ^ 2)) / ‖z.val-p‖ ^ 2) := by
  have hv : Continuous (fun z : {z : E // z ≠ p} ↦ z.val - p) :=
    continuous_subtype_val.sub continuous_const
  have hb : Continuous (fun z : {z : E // z ≠ p} ↦ inner ℝ p (z.val-p)) :=
    continuous_const.inner hv
  have hc : Continuous (fun z : {z : E // z ≠ p} ↦ ‖z.val-p‖ ^ 2) := hv.norm.pow 2
  exact (hb.neg.add ((hb.pow 2).add (continuous_const.mul hc)).sqrt).div hc
    (fun z ↦ pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr z.property)))

end HolomorphicAnosov
