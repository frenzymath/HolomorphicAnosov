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
import HolomorphicAnosov.Analysis.Flow.HasFDerivAtInitialOfVariationalOde

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology NNReal

namespace FirstVariationalDefect
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Negative-time reversal of the actual nonlinear and linear IVPs. This is not a global
flow or an extension beyond the given closed time segment. -/
theorem hasFDerivAt_initial_of_variational_ode_negative
    (F : E → E) (B U : Set E) (hB : IsCompact B) (hconv : Convex ℝ B)
    (hdiff : ∀ q ∈ B, DifferentiableAt ℝ F q)
    (hDF : ContinuousOn (fderiv ℝ F) B)
    (K : ℝ≥0) (hK : ∀ q ∈ B, ‖fderiv ℝ F q‖ ≤ K)
    (α : E → ℝ → E) (hU : IsOpen U) (x : E) (hx : x ∈ U)
    (T : ℝ) (hT : T ≤ 0)
    (hα : ∀ z ∈ U, ∀ t ∈ Icc T 0, HasDerivAt (α z) (F (α z t)) t)
    (hmem : ∀ z ∈ U, ∀ t ∈ Icc T 0, α z t ∈ B)
    (hinit : ∀ z ∈ U, α z 0 = z)
    (Y : ℝ → E →L[ℝ] E) (hYinit : Y 0 = ContinuousLinearMap.id ℝ E)
    (hY : ∀ v : E, ∀ t ∈ Icc T 0,
      HasDerivAt (fun s ↦ Y s v) (fderiv ℝ F (α x t) (Y t v)) t) :
    HasFDerivAt (fun z ↦ α z T) (Y T) x := by
  have hnegderiv : ∀ q ∈ B, fderiv ℝ (fun p ↦ -F p) q = -fderiv ℝ F q := by
    intro q hq
    exact fderiv_fun_neg
  have hreverse : ∀ s ∈ Icc 0 (-T), -s ∈ Icc T 0 := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hDFneg : ContinuousOn (fderiv ℝ (fun p ↦ -F p)) B :=
    hDF.neg.congr (fun q hq ↦ hnegderiv q hq)
  have hresult := hasFDerivAt_initial_of_variational_ode (fun p ↦ -F p) B U hB hconv
    (fun q hq ↦ (hdiff q hq).neg) hDFneg K
    (fun q hq ↦ by rw [hnegderiv q hq, norm_neg]; exact hK q hq)
    (fun z s ↦ α z (-s)) hU x hx (-T) (neg_nonneg.mpr hT)
    (fun z hz s hs ↦ by
      simpa [Function.comp_def] using
        (hα z hz (-s) (hreverse s hs)).scomp s (hasDerivAt_neg s))
    (fun z hz s hs ↦ hmem z hz (-s) (hreverse s hs))
    (fun z hz ↦ by simpa using hinit z hz)
    (fun s ↦ Y (-s)) (by simpa using hYinit)
    (fun v s hs ↦ by
      rw [hnegderiv _ (hmem x hx (-s) (hreverse s hs))]
      simpa [Function.comp_def] using
        (hY v (-s) (hreverse s hs)).scomp s (hasDerivAt_neg s))
  simpa using hresult

end FirstVariationalDefect
