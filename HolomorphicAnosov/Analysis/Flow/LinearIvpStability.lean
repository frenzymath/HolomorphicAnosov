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
import HolomorphicAnosov.Analysis.Flow.LinearIvpNormBound

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology NNReal

namespace FirstVariationalDefect
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Stability of actual linear IVPs in OPERATOR norm, with a derived solution bound.
This is the quantitative input for joint continuity of the initial-data derivative. -/
theorem linear_ivp_stability
    (A A' Y Z : ℝ → E →L[ℝ] E) (T : ℝ) (hT : 0 ≤ T) (K : ℝ≥0)
    (hA : ∀ t ∈ Icc 0 T, ‖A t‖ ≤ K)
    (hA' : ∀ t ∈ Icc 0 T, ‖A' t‖ ≤ K)
    (hY : ∀ t ∈ Icc 0 T, HasDerivAt Y ((A t).comp (Y t)) t)
    (hZ : ∀ t ∈ Icc 0 T, HasDerivAt Z ((A' t).comp (Z t)) t)
    (ε : ℝ) (hε : 0 ≤ ε) (hclose : ∀ t ∈ Icc 0 T, ‖A t - A' t‖ ≤ ε)
    (hzero : Y 0 = Z 0) :
    ∀ t ∈ Icc 0 T, ‖Y t - Z t‖ ≤
      gronwallBound 0 K (ε * (‖Z 0‖ * Real.exp ((K : ℝ) * T))) t := by
  let C := ‖Z 0‖ * Real.exp ((K : ℝ) * T)
  have hZbound : ∀ t ∈ Icc 0 T, ‖Z t‖ ≤ C := by
    intro t ht
    exact (linear_ivp_norm_bound A' Z T hT K hA' hZ t ht).trans
      (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 K.coe_nonneg)) (norm_nonneg _))
  have hd : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s ↦ Y s - Z s) ((A t).comp (Y t) - (A' t).comp (Z t)) t :=
    fun t ht ↦ (hY t ht).sub (hZ t ht)
  have hc : ContinuousOn (fun s ↦ Y s - Z s) (Icc 0 T) :=
    fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt
  have hb : ∀ t ∈ Ico 0 T, ‖(A t).comp (Y t) - (A' t).comp (Z t)‖ ≤
      (K : ℝ) * ‖Y t - Z t‖ + ε * C := by
    intro t ht
    have ht' : t ∈ Icc 0 T := ⟨ht.1, ht.2.le⟩
    have heq : (A t).comp (Y t) - (A' t).comp (Z t) =
        (A t).comp (Y t - Z t) + (A t - A' t).comp (Z t) := by
      ext v
      simp only [ContinuousLinearMap.comp_apply, sub_apply, add_apply, map_sub]
      abel
    rw [heq]
    calc
      ‖(A t).comp (Y t - Z t) + (A t - A' t).comp (Z t)‖ ≤
          ‖(A t).comp (Y t - Z t)‖ + ‖(A t - A' t).comp (Z t)‖ := norm_add_le _ _
      _ ≤ (K : ℝ) * ‖Y t - Z t‖ + ε * C := by
        apply add_le_add
        · exact ((A t).opNorm_comp_le _).trans
            (mul_le_mul_of_nonneg_right (hA t ht') (norm_nonneg _))
        · exact ((A t - A' t).opNorm_comp_le _).trans
            (mul_le_mul (hclose t ht') (hZbound t ht') (norm_nonneg _) hε)
  intro t ht
  simpa only [sub_zero] using
    norm_le_gronwallBound_of_norm_deriv_right_le hc
      (fun s hs ↦ (hd s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt)
      (by simp [hzero]) hb t ht

end FirstVariationalDefect
