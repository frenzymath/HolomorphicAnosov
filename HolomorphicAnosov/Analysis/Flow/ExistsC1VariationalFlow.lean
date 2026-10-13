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
import HolomorphicAnosov.Analysis.Flow.HasDerivAtIntegralEq
import HolomorphicAnosov.Analysis.Flow.FirstVariationOfJointIntegralWitnesses
import HolomorphicAnosov.Analysis.Flow.ExistsPicardVariationalIntegralWitnesses

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology _root_.Topology NNReal

namespace HolomorphicAnosov.W07FiniteFlowBootstrap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Closed first-variation binder from an original open finite-dimensional C¹ field, with
no integral-solution or variational-solution premise. Actual Mathlib Picard witnesses supply
both families; the normalized-defect proof supplies spatial differentiability and continuity.
The final open time interval is HALF the common witness interval, so all FTC endpoint germs
and compact two-sided variation estimates lie in the original interval. -/
theorem exists_c1_variational_flow [FiniteDimensional ℝ E]
    (F : E → E) (Ω : Set E) (hΩ : IsOpen Ω) (hF : ContDiffOn ℝ 1 F Ω)
    (x₀ : E) (hx₀ : x₀ ∈ Ω) :
    ∃ r > 0, ∃ S > 0, ∃ α : E → ℝ → E, ∃ Y : E → ℝ → E →L[ℝ] E,
      ContinuousOn (fun p : E × ℝ ↦ α p.1 p.2) (ball x₀ r ×ˢ Ioo (-S) S) ∧
      (∀ z ∈ ball x₀ r, ∀ t ∈ Ioo (-S) S, α z t ∈ Ω) ∧
      (∀ z ∈ ball x₀ r, α z 0 = z) ∧
      (∀ z ∈ ball x₀ r, ∀ t ∈ Ioo (-S) S, HasDerivAt (α z) (F (α z t)) t) ∧
      (∀ z ∈ ball x₀ r, ∀ t ∈ Ioo (-S) S,
        HasFDerivAt (fun q ↦ α q t) (Y z t) z) ∧
      ContinuousOn (fun p : E × ℝ ↦ Y p.1 p.2) (ball x₀ r ×ˢ Ioo (-S) S) ∧
      (∀ z ∈ ball x₀ r, Y z 0 = ContinuousLinearMap.id ℝ E) ∧
      (∀ z ∈ ball x₀ r, ∀ t ∈ Ioo (-S) S,
        HasDerivAt (Y z) ((fderiv ℝ F (α z t)).comp (Y z t)) t) := by
  classical
  obtain ⟨a, ha, r, hr, hra, hBΩ, S₀, hS₀, α, Y, hαcont, hmem,
      hinit, hαsol, hYcont, hYsol⟩ :=
    PicardVariationalWitnesses.exists_picard_variational_integral_witnesses F Ω hΩ hF x₀ hx₀
  let B := closedBall x₀ a
  let U := ball x₀ r
  let S := S₀ / 2
  have hS : 0 < S := half_pos hS₀
  have hSS₀ : S < S₀ := half_lt_self hS₀
  have hsub : Ioo (-S) S ⊆ Ioo (-S₀) S₀ := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hdiff : ∀ q ∈ B, DifferentiableAt ℝ F q := fun q hq ↦
    ((hF q (hBΩ hq)).contDiffAt (hΩ.mem_nhds (hBΩ hq))).differentiableAt one_ne_zero
  have hDF : ContinuousOn (fderiv ℝ F) B :=
    (hF.continuousOn_fderiv_of_isOpen hΩ (by norm_num)).mono hBΩ
  have hvariation := FirstVariationalDefect.first_variation_of_joint_integral_witnesses
    F B U (isCompact_closedBall _ _) (convex_closedBall _ _) hdiff hDF
    α isOpen_ball S₀ hαcont hmem hαsol Y
    (fun z hz ↦ (hYcont z hz).continuousOn) hYsol S hS hSS₀
  have hYjoint : ContinuousOn (fun p : E × ℝ ↦ Y p.1 p.2) (U ×ˢ Ioo (-S) S) :=
    (hvariation.2.mono (prod_mono Subset.rfl Ioo_subset_Icc_self)).congr
      (fun p hp ↦ ((hvariation.1 p.1 hp.1 p.2 (Ioo_subset_Icc_self hp.2)).fderiv).symm)
  have hαtime : ∀ z ∈ U, ContinuousOn (α z) (Ioo (-S₀) S₀) := by
    intro z hz
    simpa only [Function.comp_def, id_eq] using hαcont.comp
      (continuous_const.prodMk continuous_id).continuousOn (fun _ ht ↦ ⟨hz, ht⟩)
  have hzero : (0 : ℝ) ∈ Ioo (-S₀) S₀ := ⟨neg_lt_zero.mpr hS₀, hS₀⟩
  have hFc : ContinuousOn F B := fun q hq ↦
    (hdiff q hq).continuousAt.continuousWithinAt
  have hODE : ∀ z ∈ U, ∀ t ∈ Ioo (-S) S, HasDerivAt (α z) (F (α z t)) t := by
    intro z hz t ht
    apply FirstVariationalDefect.hasDerivAt_of_integral_eq (α z) (fun s ↦ F (α z s))
      (Ioo (-S₀) S₀) isOpen_Ioo (hFc.comp (hαtime z hz) (hmem z hz)) 0 t (hsub ht)
      (ordConnected_Ioo.uIcc_subset hzero (hsub ht))
    intro s hs
    simpa only [hinit z hz] using hαsol z hz s hs
  refine ⟨r, hr, S, hS, α, Y, hαcont.mono (prod_mono Subset.rfl hsub), ?_,
    hinit, hODE, ?_, hYjoint, ?_, ?_⟩
  · intro z hz t ht
    exact hBΩ (hmem z hz t (hsub ht))
  · intro z hz t ht
    exact hvariation.1 z hz t (Ioo_subset_Icc_self ht)

  · intro z hz
    have hh := hYsol z hz 0 hzero
    simpa using hh
  · intro z hz t ht
    have hcoeff : ContinuousOn
        (fun s ↦ (fderiv ℝ F (α z s)).comp (Y z s)) (Ioo (-S₀) S₀) :=
      (hDF.comp (hαtime z hz) (hmem z hz)).clm_comp (hYcont z hz).continuousOn
    apply FirstVariationalDefect.hasDerivAt_of_integral_eq (Y z)
      (fun s ↦ (fderiv ℝ F (α z s)).comp (Y z s))
      (Ioo (-S₀) S₀) isOpen_Ioo hcoeff 0 t (hsub ht)
      (ordConnected_Ioo.uIcc_subset hzero (hsub ht))
    intro u hu
    simpa only [show Y z 0 = ContinuousLinearMap.id ℝ E by
      have hh := hYsol z hz 0 hzero; simpa using hh] using hYsol z hz u hu

end HolomorphicAnosov.W07FiniteFlowBootstrap
