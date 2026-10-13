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
import HolomorphicAnosov.Analysis.Flow.UniformTaylorRemainder
import HolomorphicAnosov.Analysis.Flow.NormalizedDefectBound
import HolomorphicAnosov.Analysis.Flow.GronwallForcingHomogeneous

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology NNReal

namespace FirstVariationalDefect
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Initial-data differentiability of the SAME nonlinear solution from actual nonlinear and
linear IVP witnesses on a common compact convex buffer. The only derivative of `α` assumed
is its time derivative. The full initial-data derivative is the conclusion.

This is the positive-time defect argument of Teschl pp.46--47. An open initial set allows
the arbitrary small initial increments used by the Fréchet derivative. Time derivatives at
closed-interval endpoints are supplied by the open time domain of a local integral solution. -/
theorem hasFDerivAt_initial_of_variational_ode
    (F : E → E) (B U : Set E) (hB : IsCompact B) (hconv : Convex ℝ B)
    (hdiff : ∀ q ∈ B, DifferentiableAt ℝ F q)
    (hDF : ContinuousOn (fderiv ℝ F) B)
    (K : ℝ≥0) (hK : ∀ q ∈ B, ‖fderiv ℝ F q‖ ≤ K)
    (α : E → ℝ → E) (hU : IsOpen U) (x : E) (hx : x ∈ U)
    (T : ℝ) (hT : 0 ≤ T)
    (hα : ∀ z ∈ U, ∀ t ∈ Icc 0 T, HasDerivAt (α z) (F (α z t)) t)
    (hmem : ∀ z ∈ U, ∀ t ∈ Icc 0 T, α z t ∈ B)
    (hinit : ∀ z ∈ U, α z 0 = z)
    (Y : ℝ → E →L[ℝ] E) (hYinit : Y 0 = ContinuousLinearMap.id ℝ E)
    (hY : ∀ v : E, ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s ↦ Y s v) (fderiv ℝ F (α x t) (Y t v)) t) :
    HasFDerivAt (fun z ↦ α z T) (Y T) x := by
  let C : ℝ := Real.exp (K * T)
  have hC : 0 < C := Real.exp_pos _
  have hLip : LipschitzOnWith K F B :=
    hconv.lipschitzOnWith_of_nnnorm_fderiv_le hdiff
      (fun q hq ↦ by exact_mod_cast hK q hq)
  have hgap : ∀ z ∈ U, ∀ t ∈ Icc 0 T, ‖α z t - α x t‖ ≤ C * ‖z - x‖ := by
    intro z hz t ht
    have hc z hz : ContinuousOn (α z) (Icc 0 T) :=
      fun s hs ↦ (hα z hz s hs).continuousAt.continuousWithinAt
    have h := dist_le_of_trajectories_ODE_of_mem
      (v := fun _ ↦ F) (s := fun _ ↦ B) (fun _ _ ↦ hLip)
      (hc z hz) (fun s hs ↦ (hα z hz s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt)
      (fun s hs ↦ hmem z hz s ⟨hs.1, hs.2.le⟩)
      (hc x hx) (fun s hs ↦ (hα x hx s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt)
      (fun s hs ↦ hmem x hx s ⟨hs.1, hs.2.le⟩)
      (δ := ‖z - x‖) (by simp [hinit z hz, hinit x hx, dist_eq_norm]) t ht
    have hexp : Real.exp ((K : ℝ) * t) ≤ C :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 K.coe_nonneg)
    simp only [sub_zero, dist_eq_norm] at h
    simpa only [mul_comm C] using
      h.trans (mul_le_mul_of_nonneg_left hexp (norm_nonneg (z - x)))
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  let G := |gronwallBound 0 K 1 T| + 1
  have hG : 0 < G := by dsimp [G]; positivity
  let ε := c / (C * G)
  have hε : 0 < ε := div_pos hc (mul_pos hC hG)
  obtain ⟨δ, hδ, htaylor⟩ := uniform_taylor_remainder F B hB hconv hdiff hDF ε hε
  have hnear : ∀ᶠ h : E in 𝓝 0, x + h ∈ U := by
    have ht : Tendsto (fun h : E ↦ x + h) (𝓝 0) (𝓝 x) := by
      have hc : ContinuousAt (fun h : E ↦ x + h) 0 := by fun_prop
      simpa only [add_zero] using hc.tendsto
    exact ht (hU.mem_nhds hx)
  have hsmall : ∀ᶠ h : E in 𝓝 0, ‖h‖ < δ / C := by
    filter_upwards [Metric.ball_mem_nhds (0 : E) (div_pos hδ hC)] with h hh
    simpa only [Metric.mem_ball, dist_zero_right] using hh
  filter_upwards [hnear, hsmall] with h hhu hhs
  by_cases hh : h = 0
  · simp [hh]
  have hn : 0 < ‖h‖ := norm_pos_iff.mpr hh
  have hgh : ∀ t ∈ Icc 0 T, ‖α (x + h) t - α x t‖ ≤ C * ‖h‖ := by
    intro t ht
    simpa using hgap (x + h) hhu t ht
  have hb := normalized_defect_bound F (α x) (α (x + h)) (fun t ↦ Y t h)
    (fun t ↦ fderiv ℝ F (α x t)) T K ε C hT K.coe_nonneg hε.le hC.le h hh
    (hα x hx) (hα (x + h) hhu) (hY h)
    (by simp [hinit x hx, hinit (x + h) hhu])
    (by simp [hYinit])
    (fun t ht ↦ hK _ (hmem x hx t ht)) hgh
    (fun t ht ↦ htaylor _ (hmem x hx t ht) _ (hmem (x + h) hhu t ht) (by
      rw [dist_eq_norm]
      have hsmall' : C * ‖h‖ < δ := by
        simpa only [mul_comm] using (lt_div_iff₀ hC).mp hhs
      exact (hgh t ht).trans_lt hsmall'))
  have hforcing : gronwallBound 0 K (ε * C) T ≤ c := by
    rw [gronwall_forcing_homogeneous]
    calc
      ε * C * gronwallBound 0 K 1 T ≤ ε * C * G := by
        gcongr
        exact (le_abs_self _).trans (by dsimp [G]; linarith)
      _ = c := by dsimp [ε]; field_simp
  have hb' : ‖h‖⁻¹ * ‖α (x + h) T - α x T - Y T h‖ ≤ c := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)] using
      hb.trans hforcing
  calc
    ‖α (x + h) T - α x T - Y T h‖ =
        ‖h‖ * (‖h‖⁻¹ * ‖α (x + h) T - α x T - Y T h‖) := by field_simp
    _ ≤ ‖h‖ * c := mul_le_mul_of_nonneg_left hb' hn.le
    _ = c * ‖h‖ := mul_comm _ _

end FirstVariationalDefect
