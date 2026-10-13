import Mathlib.Probability.Moments.Variance

/-!
# Equality in the unit-interval Schwarz estimate

Source: Lehto–Virtanen, *Quasiconformal Mappings in the Plane* (1973),
Chapter I §4.3, p.23, the necessity argument for equality in Rengel’s inequality.
DAG node: `analysis.qc_rengel_slice_equality_g11`.
-/

namespace HolomorphicAnosov
open Set MeasureTheory

/-- Equality in the unit-interval Schwarz estimate forces a continuous square-integrable
speed to be constant at every interior point. Source: Lehto–Virtanen (1973), I.§4.3,
p.23, equality in the vertical slice estimate of the inverse canonical map.

Proof: the restriction of Lebesgue measure to (0,1) is a probability measure. The
assumed equality says its variance is zero. Thus the speed equals its mean almost
everywhere. Both sides are continuous on the open interval, so equality holds there
everywhere. No value or derivative at either endpoint is required. -/
theorem qc_rengel_slice_equality {v : ℝ → ℝ}
    (hc : ContinuousOn v (Ioo 0 1))
    (hv : MemLp v 2 (volume.restrict (Ioo 0 1)))
    (heq : (∫ t in Ioo (0 : ℝ) 1, v t ^ 2) = (∫ t in Ioo (0 : ℝ) 1, v t) ^ 2) :
    ∀ t ∈ Ioo (0 : ℝ) 1, v t = ∫ s in Ioo (0 : ℝ) 1, v s := by
  have : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) :=
    ⟨by simp⟩
  have hvar : ProbabilityTheory.variance v (volume.restrict (Ioo (0 : ℝ) 1)) = 0 := by
    rw [ProbabilityTheory.variance_eq_sub hv]
    change (∫ t in Ioo (0 : ℝ) 1, v t ^ 2) - (∫ t in Ioo (0 : ℝ) 1, v t) ^ 2 = 0
    rw [heq, sub_self]
  exact Measure.eqOn_open_of_ae_eq
    (ProbabilityTheory.ae_eq_integral_of_variance_eq_zero hv hvar)
    isOpen_Ioo hc continuousOn_const

end HolomorphicAnosov
