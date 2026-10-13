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
import HolomorphicAnosov.Analysis.Flow.FirstVariationAndJointDerivativeContinuitySymmetric

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology NNReal

namespace FirstVariationalDefect
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- End-to-end first variation for the SAME continuous Picard family and actual linear
integral-IVP family. On each strictly interior two-sided compact time rectangle the spatial
derivative exists and is jointly continuous. Only the linear witness's separate TIME
continuity is assumed; its initial-parameter continuity is proved by operator-norm stability.

This is the first-variation mechanism of Teschl pp.46--47. Existence of either integral
witness is a separate obligation. The conclusion is not the full smooth local-flow theorem. -/
theorem first_variation_of_joint_integral_witnesses [CompleteSpace E]
    (F : E → E) (B U : Set E) (hB : IsCompact B) (hconv : Convex ℝ B)
    (hdiff : ∀ q ∈ B, DifferentiableAt ℝ F q)
    (hDF : ContinuousOn (fderiv ℝ F) B)
    (α : E → ℝ → E) (hU : IsOpen U) (S : ℝ)
    (hαcont : ContinuousOn (fun p : E × ℝ ↦ α p.1 p.2) (U ×ˢ Ioo (-S) S))
    (hmem : ∀ z ∈ U, ∀ t ∈ Ioo (-S) S, α z t ∈ B)
    (hαsol : ∀ z ∈ U, ∀ t ∈ Ioo (-S) S,
      α z t = z + ∫ s in 0..t, F (α z s))
    (Y : E → ℝ → E →L[ℝ] E)
    (hYcont : ∀ z ∈ U, ContinuousOn (Y z) (Ioo (-S) S))
    (hYsol : ∀ z ∈ U, ∀ t ∈ Ioo (-S) S,
      Y z t = ContinuousLinearMap.id ℝ E +
        ∫ s in 0..t, (fderiv ℝ F (α z s)).comp (Y z s))
    (T : ℝ) (hT : 0 < T) (hTS : T < S) :
    (∀ z ∈ U, ∀ t ∈ Icc (-T) T, HasFDerivAt (fun q ↦ α q t) (Y z t) z) ∧
    ContinuousOn (fun p : E × ℝ ↦ fderiv ℝ (fun q ↦ α q p.2) p.1)
      (U ×ˢ Icc (-T) T) := by
  have hS : 0 < S := hT.trans hTS
  have hzero : (0 : ℝ) ∈ Ioo (-S) S := ⟨neg_lt_zero.mpr hS, hS⟩
  have hseg : Icc (-T) T ⊆ Ioo (-S) S := Icc_subset_Ioo (neg_lt_neg hTS) hTS
  have htime : ∀ z ∈ U, ContinuousOn (α z) (Ioo (-S) S) := by
    intro z hz
    simpa only [Function.comp_def, id_eq] using hαcont.comp
      (continuous_const.prodMk continuous_id).continuousOn (fun _ ht ↦ ⟨hz, ht⟩)
  have hinit : ∀ z ∈ U, α z 0 = z := by
    intro z hz
    simpa using hαsol z hz 0 hzero
  have hYinit : ∀ z ∈ U, Y z 0 = ContinuousLinearMap.id ℝ E := by
    intro z hz
    simpa using hYsol z hz 0 hzero
  have hFcont : ContinuousOn F B := fun q hq ↦
    (hdiff q hq).continuousAt.continuousWithinAt
  have hαode : ∀ z ∈ U, ∀ t ∈ Icc (-T) T,
      HasDerivAt (α z) (F (α z t)) t := by
    intro z hz t ht
    apply hasDerivAt_of_integral_eq (α z) (fun s ↦ F (α z s)) (Ioo (-S) S)
      isOpen_Ioo (hFcont.comp (htime z hz) (hmem z hz)) 0 t (hseg ht)
      (ordConnected_Ioo.uIcc_subset hzero (hseg ht))
    intro s hs
    simpa only [hinit z hz] using hαsol z hz s hs
  have hYode : ∀ z ∈ U, ∀ t ∈ Icc (-T) T,
      HasDerivAt (Y z) ((fderiv ℝ F (α z t)).comp (Y z t)) t := by
    intro z hz t ht
    apply hasDerivAt_of_integral_eq (Y z)
      (fun s ↦ (fderiv ℝ F (α z s)).comp (Y z s)) (Ioo (-S) S) isOpen_Ioo
      ((hDF.comp (htime z hz) (hmem z hz)).clm_comp (hYcont z hz))
      0 t (hseg ht) (ordConnected_Ioo.uIcc_subset hzero (hseg ht))
    intro s hs
    simpa only [hYinit z hz] using hYsol z hz s hs
  exact first_variation_and_joint_derivative_continuity_symmetric F B U hB hconv hdiff hDF
    α hU (Ioo (-S) S) isOpen_Ioo hαcont hmem T hT hseg hαode hinit Y hYinit hYode

end FirstVariationalDefect
