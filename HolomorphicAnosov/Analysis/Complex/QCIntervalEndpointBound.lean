import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

namespace HolomorphicAnosov
open Set Filter _root_.Topology
open scoped ContDiff
open MeasureTheory

/-- The endpoint estimate used in Lehto–Virtanen I.Theorem 3.1, pp.18–19.
It is stated with the derivative integrability exposed as an interface: this is exactly
what the source obtains from the continuous interior derivative and the finite rectangle.
No derivative at either endpoint is required. -/
theorem qc_slice_endpoint_bound
    {a b : ℝ} {f f' : ℝ → ℂ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hint : IntervalIntegrable f' volume a b) :
    ‖f b - f a‖ ≤ ∫ x in a..b, ‖f' x‖ := by
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hint]
  exact intervalIntegral.norm_integral_le_integral_norm hab


end HolomorphicAnosov
