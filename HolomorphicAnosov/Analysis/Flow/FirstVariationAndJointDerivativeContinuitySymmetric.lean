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
import HolomorphicAnosov.Analysis.Flow.HasFDerivAtInitialOfVariationalOdeNegative
import HolomorphicAnosov.Analysis.Flow.LinearIvpJointContinuousOnSymmetric

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology NNReal

namespace FirstVariationalDefect
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two-sided first variation and joint continuity of the actual spatial derivative on the
same buffered rectangle. The nonlinear family is only jointly continuous and a time ODE
witness. The actual operator-valued linear IVP is differentiated only in time. Compact bounds,
initial-data differentiability, and parameter continuity of the linear IVP are derived. -/
theorem first_variation_and_joint_derivative_continuity_symmetric
    (F : E → E) (B U : Set E) (hB : IsCompact B) (hconv : Convex ℝ B)
    (hdiff : ∀ q ∈ B, DifferentiableAt ℝ F q)
    (hDF : ContinuousOn (fderiv ℝ F) B)
    (α : E → ℝ → E) (hU : IsOpen U) (I : Set ℝ) (hI : IsOpen I)
    (hαcont : ContinuousOn (fun p : E × ℝ ↦ α p.1 p.2) (U ×ˢ I))
    (hmem : ∀ z ∈ U, ∀ t ∈ I, α z t ∈ B)
    (T : ℝ) (hT : 0 < T) (hseg : Icc (-T) T ⊆ I)
    (hα : ∀ z ∈ U, ∀ t ∈ Icc (-T) T, HasDerivAt (α z) (F (α z t)) t)
    (hinit : ∀ z ∈ U, α z 0 = z)
    (Y : E → ℝ → E →L[ℝ] E)
    (hYinit : ∀ z ∈ U, Y z 0 = ContinuousLinearMap.id ℝ E)
    (hY : ∀ z ∈ U, ∀ t ∈ Icc (-T) T,
      HasDerivAt (Y z) ((fderiv ℝ F (α z t)).comp (Y z t)) t) :
    (∀ z ∈ U, ∀ t ∈ Icc (-T) T, HasFDerivAt (fun q ↦ α q t) (Y z t) z) ∧
    ContinuousOn (fun p : E × ℝ ↦ fderiv ℝ (fun q ↦ α q p.2) p.1)
      (U ×ˢ Icc (-T) T) := by
  obtain ⟨L, hL⟩ := hB.exists_bound_of_continuousOn hDF
  let K : ℝ≥0 := ⟨max L 0, le_max_right _ _⟩
  have hK : ∀ q ∈ B, ‖fderiv ℝ F q‖ ≤ K := fun q hq ↦
    (hL q hq).trans (le_max_left _ _)
  have hYeval : ∀ z ∈ U, ∀ v : E, ∀ t ∈ Icc (-T) T,
      HasDerivAt (fun s ↦ Y z s v) (fderiv ℝ F (α z t) (Y z t v)) t := by
    intro z hz v t ht
    simpa using (hY z hz t ht).clm_apply (hasDerivAt_const t v)
  have hfirst : ∀ z ∈ U, ∀ t ∈ Icc (-T) T,
      HasFDerivAt (fun q ↦ α q t) (Y z t) z := by
    intro z hz t ht
    by_cases hpos : 0 ≤ t
    · have hsub : Icc 0 t ⊆ Icc (-T) T := fun _ hs ↦
        ⟨(neg_nonpos.mpr hT.le).trans hs.1, hs.2.trans ht.2⟩
      exact hasFDerivAt_initial_of_variational_ode F B U hB hconv hdiff hDF K hK
        α hU z hz t hpos
        (fun q hq s hs ↦ hα q hq s (hsub hs))
        (fun q hq s hs ↦ hmem q hq s (hseg (hsub hs))) hinit (Y z) (hYinit z hz)
        (fun v s hs ↦ hYeval z hz v s (hsub hs))
    · have hsub : Icc t 0 ⊆ Icc (-T) T := fun _ hs ↦
        ⟨ht.1.trans hs.1, hs.2.trans hT.le⟩
      exact hasFDerivAt_initial_of_variational_ode_negative F B U hB hconv hdiff hDF K hK
        α hU z hz t (le_of_not_ge hpos)
        (fun q hq s hs ↦ hα q hq s (hsub hs))
        (fun q hq s hs ↦ hmem q hq s (hseg (hsub hs))) hinit (Y z) (hYinit z hz)
        (fun v s hs ↦ hYeval z hz v s (hsub hs))
  have hcoef : ContinuousOn (fun p : E × ℝ ↦ fderiv ℝ F (α p.1 p.2)) (U ×ˢ I) :=
    hDF.comp hαcont (fun p hp ↦ hmem p.1 hp.1 p.2 hp.2)
  have hYcont := linear_ivp_joint_continuousOn_symmetric
    (fun p : E × ℝ ↦ fderiv ℝ F (α p.1 p.2)) Y U I hU hI hcoef T hT hseg K
    (fun z hz t ht ↦ hK _ (hmem z hz t (hseg ht))) hY
    (ContinuousLinearMap.id ℝ E) hYinit
  exact ⟨hfirst, hYcont.congr (fun p hp ↦ (hfirst p.1 hp.1 p.2 hp.2).fderiv)⟩

end FirstVariationalDefect
