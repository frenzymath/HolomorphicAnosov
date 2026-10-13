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
import HolomorphicAnosov.Analysis.Flow.LinearIvpStability
import HolomorphicAnosov.Analysis.Flow.CoefficientsUniformNearInitial

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology NNReal

namespace FirstVariationalDefect
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Uniform dependence of the actual linear IVP on its coefficient parameter, in operator
norm and uniformly over the closed time segment. No continuity of the solution in that
parameter is assumed. The coefficient continuity and IVP comparison establish it. -/
theorem linear_ivp_uniform_near_initial
    (A : E × ℝ → E →L[ℝ] E) (Y : E → ℝ → E →L[ℝ] E)
    (U : Set E) (I : Set ℝ) (hU : IsOpen U) (hI : IsOpen I)
    (hAcont : ContinuousOn A (U ×ˢ I))
    (T : ℝ) (hT : 0 ≤ T) (hseg : Icc 0 T ⊆ I) (K : ℝ≥0)
    (hA : ∀ z ∈ U, ∀ t ∈ Icc 0 T, ‖A (z, t)‖ ≤ K)
    (hY : ∀ z ∈ U, ∀ t ∈ Icc 0 T,
      HasDerivAt (Y z) ((A (z, t)).comp (Y z t)) t)
    (L : E →L[ℝ] E) (hinit : ∀ z ∈ U, Y z 0 = L)
    (x : E) (hx : x ∈ U) :
    ∀ ε > 0, ∃ δ > 0, ∀ z ∈ U, dist z x < δ → ∀ t ∈ Icc 0 T,
      ‖Y z t - Y x t‖ < ε := by
  intro ε hε
  let C := ‖Y x 0‖ * Real.exp ((K : ℝ) * T)
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hH : ContinuousAt (fun η : ℝ ↦ gronwallBound 0 K (η * C) T) 0 :=
    ((gronwallBound_continuous_ε 0 K T).comp (continuous_id.mul continuous_const)).continuousAt
  obtain ⟨r, hr, hsmall⟩ := Metric.continuousAt_iff.mp hH ε hε
  let η := r / 2
  have hη : 0 < η := half_pos hr
  have hbound : gronwallBound 0 K (η * C) T < ε := by
    have hh := hsmall (x := η) (by
      simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_pos hη] using half_lt_self hr)
    simp only [zero_mul, gronwallBound_ε0_δ0, dist_zero_right, Real.norm_eq_abs] at hh
    exact (le_abs_self _).trans_lt hh
  obtain ⟨δ, hδ, hclose⟩ :=
    coefficients_uniform_near_initial A U I hU hI hAcont x hx T hseg η hη
  refine ⟨δ, hδ, ?_⟩
  intro z hz hzx t ht
  have hb := linear_ivp_stability (fun s ↦ A (z, s)) (fun s ↦ A (x, s))
    (Y z) (Y x) T hT K (hA z hz) (hA x hx) (hY z hz) (hY x hx) η hη.le
    (fun s hs ↦ (hclose z hzx s hs).le) (by rw [hinit z hz, hinit x hx]) t ht
  exact hb.trans_lt ((gronwallBound_mono (δ := 0) (K := K) (ε := η * C)
    (le_refl 0) (mul_nonneg hη.le hC) K.coe_nonneg ht.2).trans_lt hbound)

end FirstVariationalDefect
