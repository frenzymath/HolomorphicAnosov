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
import HolomorphicAnosov.Analysis.Flow.LinearIvpJointContinuousOn

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology NNReal

namespace FirstVariationalDefect
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual spatial derivative and its joint continuity on the SAME positive-time rectangle.
The nonlinear witness is assumed only jointly continuous and a time integral curve. The
linear witness is assumed only an actual operator-valued time IVP. Initial differentiability
comes from the defect argument, and joint derivative continuity comes from linear-IVP stability.
Thus neither conclusion is an input in disguise. -/
theorem first_variation_and_joint_derivative_continuity
    (F : E → E) (B U : Set E) (hB : IsCompact B) (hconv : Convex ℝ B)
    (hdiff : ∀ q ∈ B, DifferentiableAt ℝ F q)
    (hDF : ContinuousOn (fderiv ℝ F) B)
    (α : E → ℝ → E) (hU : IsOpen U) (I : Set ℝ) (hI : IsOpen I)
    (hαcont : ContinuousOn (fun p : E × ℝ ↦ α p.1 p.2) (U ×ˢ I))
    (hmem : ∀ z ∈ U, ∀ t ∈ I, α z t ∈ B)
    (T : ℝ) (hT : 0 ≤ T) (hseg : Icc 0 T ⊆ I)
    (hα : ∀ z ∈ U, ∀ t ∈ Icc 0 T, HasDerivAt (α z) (F (α z t)) t)
    (hinit : ∀ z ∈ U, α z 0 = z)
    (Y : E → ℝ → E →L[ℝ] E)
    (hYinit : ∀ z ∈ U, Y z 0 = ContinuousLinearMap.id ℝ E)
    (hY : ∀ z ∈ U, ∀ t ∈ Icc 0 T,
      HasDerivAt (Y z) ((fderiv ℝ F (α z t)).comp (Y z t)) t) :
    (∀ z ∈ U, ∀ t ∈ Icc 0 T, HasFDerivAt (fun q ↦ α q t) (Y z t) z) ∧
    ContinuousOn (fun p : E × ℝ ↦ fderiv ℝ (fun q ↦ α q p.2) p.1)
      (U ×ˢ Icc 0 T) := by
  obtain ⟨L, hL⟩ := hB.exists_bound_of_continuousOn hDF
  let K : ℝ≥0 := ⟨max L 0, le_max_right _ _⟩
  have hK : ∀ q ∈ B, ‖fderiv ℝ F q‖ ≤ K := fun q hq ↦
    (hL q hq).trans (le_max_left _ _)
  have hfirst : ∀ z ∈ U, ∀ t ∈ Icc 0 T,
      HasFDerivAt (fun q ↦ α q t) (Y z t) z := by
    intro z hz t ht
    have hsub : Icc 0 t ⊆ Icc 0 T := fun _ hs ↦ ⟨hs.1, hs.2.trans ht.2⟩
    apply hasFDerivAt_initial_of_variational_ode F B U hB hconv hdiff hDF K hK
      α hU z hz t ht.1
      (fun q hq s hs ↦ hα q hq s (hsub hs))
      (fun q hq s hs ↦ hmem q hq s (hseg (hsub hs))) hinit (Y z) (hYinit z hz)
    intro v s hs
    simpa using (hY z hz s (hsub hs)).clm_apply (hasDerivAt_const s v)
  have hcoef : ContinuousOn (fun p : E × ℝ ↦ fderiv ℝ F (α p.1 p.2)) (U ×ˢ I) :=
    hDF.comp hαcont (fun p hp ↦ hmem p.1 hp.1 p.2 hp.2)
  have hYcont := linear_ivp_joint_continuousOn
    (fun p : E × ℝ ↦ fderiv ℝ F (α p.1 p.2)) Y U I hU hI hcoef T hT hseg K
    (fun z hz t ht ↦ hK _ (hmem z hz t (hseg ht))) hY
    (ContinuousLinearMap.id ℝ E) hYinit
  exact ⟨hfirst, hYcont.congr (fun p hp ↦ (hfirst p.1 hp.1 p.2 hp.2).fderiv)⟩

end FirstVariationalDefect
