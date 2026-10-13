import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology NNReal

namespace FirstVariationalDefect
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Operator-norm bound for an actual linear variational IVP. It supplies the compact-time
matrix bound used in the continuity argument, without assuming boundedness of the solution. -/
theorem linear_ivp_norm_bound
    (A Y : ℝ → E →L[ℝ] E) (T : ℝ) (_hT : 0 ≤ T) (K : ℝ≥0)
    (hA : ∀ t ∈ Icc 0 T, ‖A t‖ ≤ K)
    (hY : ∀ t ∈ Icc 0 T, HasDerivAt Y ((A t).comp (Y t)) t) :
    ∀ t ∈ Icc 0 T, ‖Y t‖ ≤ ‖Y 0‖ * Real.exp ((K : ℝ) * t) := by
  have hc : ContinuousOn Y (Icc 0 T) :=
    fun t ht ↦ (hY t ht).continuousAt.continuousWithinAt
  intro t ht
  simpa only [gronwallBound_ε0, sub_zero] using
    norm_le_gronwallBound_of_norm_deriv_right_le hc
      (fun s hs ↦ (hY s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt) (le_rfl : ‖Y 0‖ ≤ ‖Y 0‖)
      (ε := 0) (K := K) (fun s hs ↦ by
        simpa only [add_zero] using ((A s).opNorm_comp_le (Y s)).trans
          (mul_le_mul_of_nonneg_right (hA s ⟨hs.1, hs.2.le⟩) (norm_nonneg _))) t ht

end FirstVariationalDefect
