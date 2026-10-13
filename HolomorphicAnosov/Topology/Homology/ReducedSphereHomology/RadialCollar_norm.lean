import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

/-- The norm calculation in Hatcher's radial good-pair deformation.
The denominator is positive on the actual collar. -/
theorem radialCollar_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (hx : 0 < ‖x‖) (t : unitInterval) :
    ‖((1 - (t : ℝ)) + (t : ℝ) / ‖x‖) • x‖ =
      (1 - (t : ℝ)) * ‖x‖ + (t : ℝ) := by
  have hc : 0 ≤ (1 - (t : ℝ)) + (t : ℝ) / ‖x‖ :=
    add_nonneg (sub_nonneg.mpr t.property.2) (div_nonneg t.property.1 hx.le)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, add_mul,
    div_mul_cancel₀ _ hx.ne']

end HolomorphicAnosov.Topology.Homology
