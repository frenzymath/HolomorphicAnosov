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
import HolomorphicAnosov.Analysis.Flow.HasDerivAtIntegralEq
import HolomorphicAnosov.Analysis.Flow.HasFDerivAtInitialOfVariationalOdeNegative

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology NNReal

namespace FirstVariationalDefect
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The first variational derivative of a continuous Picard integral solution, on its SAME
open initial/time rectangle. Both nonlinear and linear witnesses are given by their actual
integral equations. Compactness derives the field derivative bound; Grönwall derives initial
Lipschitz dependence; the normalized defect proves the spatial derivative. Negative times
are handled by reversal of both witnesses, so no one-sided derivative is substituted.

Only continuity in TIME of the linear witness is assumed; no spatial regularity of `α`,
no joint continuity of `Y`, and no differentiability of Picard approximants is a premise. -/
theorem hasFDerivAt_initial_of_integral_witnesses [CompleteSpace E]
    (F : E → E) (B U : Set E) (hB : IsCompact B) (hconv : Convex ℝ B)
    (hdiff : ∀ q ∈ B, DifferentiableAt ℝ F q)
    (hDF : ContinuousOn (fderiv ℝ F) B)
    (α : E → ℝ → E) (hU : IsOpen U) (x : E) (hx : x ∈ U)
    (S : ℝ) (hS : 0 < S)
    (hαcont : ∀ z ∈ U, ContinuousOn (α z) (Ioo (-S) S))
    (hmem : ∀ z ∈ U, ∀ t ∈ Ioo (-S) S, α z t ∈ B)
    (hαsol : ∀ z ∈ U, ∀ t ∈ Ioo (-S) S,
      α z t = z + ∫ s in 0..t, F (α z s))
    (Y : ℝ → E →L[ℝ] E) (hYcont : ContinuousOn Y (Ioo (-S) S))
    (hYsol : ∀ v : E, ∀ t ∈ Ioo (-S) S,
      Y t v = v + ∫ s in 0..t, fderiv ℝ F (α x s) (Y s v))
    (T : ℝ) (hT : T ∈ Ioo (-S) S) :
    HasFDerivAt (fun z ↦ α z T) (Y T) x := by
  have hzero : (0 : ℝ) ∈ Ioo (-S) S := ⟨neg_lt_zero.mpr hS, hS⟩
  have hinit : ∀ z ∈ U, α z 0 = z := by
    intro z hz
    simpa using hαsol z hz 0 hzero
  have hYinit : Y 0 = ContinuousLinearMap.id ℝ E := by
    ext v
    simpa using hYsol v 0 hzero
  have hFcont : ContinuousOn F B := fun q hq ↦
    (hdiff q hq).continuousAt.continuousWithinAt
  have hαode : ∀ z ∈ U, ∀ t ∈ Ioo (-S) S,
      HasDerivAt (α z) (F (α z t)) t := by
    intro z hz t ht
    apply hasDerivAt_of_integral_eq (α z) (fun s ↦ F (α z s)) (Ioo (-S) S)
      isOpen_Ioo (hFcont.comp (hαcont z hz) (hmem z hz)) 0 t ht
      (ordConnected_Ioo.uIcc_subset hzero ht)
    intro s hs
    simpa only [hinit z hz] using hαsol z hz s hs
  have hYode : ∀ v : E, ∀ t ∈ Ioo (-S) S,
      HasDerivAt (fun s ↦ Y s v) (fderiv ℝ F (α x t) (Y t v)) t := by
    intro v t ht
    apply hasDerivAt_of_integral_eq (fun s ↦ Y s v)
      (fun s ↦ fderiv ℝ F (α x s) (Y s v)) (Ioo (-S) S) isOpen_Ioo
      ((hDF.comp (hαcont x hx) (hmem x hx)).clm_apply
        (hYcont.clm_apply continuousOn_const)) 0 t ht
      (ordConnected_Ioo.uIcc_subset hzero ht)
    intro s hs
    simpa only [hYinit, ContinuousLinearMap.id_apply] using hYsol v s hs
  obtain ⟨L, hL⟩ := hB.exists_bound_of_continuousOn hDF
  let K : ℝ≥0 := ⟨max L 0, le_max_right _ _⟩
  have hK : ∀ q ∈ B, ‖fderiv ℝ F q‖ ≤ K := fun q hq ↦
    (hL q hq).trans (le_max_left _ _)
  by_cases hpos : 0 ≤ T
  · have hinterval : Icc 0 T ⊆ Ioo (-S) S :=
      Icc_subset_Ioo hzero.1 hT.2
    exact hasFDerivAt_initial_of_variational_ode F B U hB hconv hdiff hDF K hK
      α hU x hx T hpos
      (fun z hz t ht ↦ hαode z hz t (hinterval ht))
      (fun z hz t ht ↦ hmem z hz t (hinterval ht)) hinit Y hYinit
      (fun v t ht ↦ hYode v t (hinterval ht))
  · have hinterval : Icc T 0 ⊆ Ioo (-S) S :=
      Icc_subset_Ioo hT.1 hzero.2
    exact hasFDerivAt_initial_of_variational_ode_negative F B U hB hconv hdiff hDF K hK
      α hU x hx T (le_of_not_ge hpos)
      (fun z hz t ht ↦ hαode z hz t (hinterval ht))
      (fun z hz t ht ↦ hmem z hz t (hinterval ht)) hinit Y hYinit
      (fun v t ht ↦ hYode v t (hinterval ht))

end FirstVariationalDefect
