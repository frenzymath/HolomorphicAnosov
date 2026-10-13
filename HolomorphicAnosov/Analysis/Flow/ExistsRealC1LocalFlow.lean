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
import HolomorphicAnosov.Analysis.JointRealPartialDerivative
import HolomorphicAnosov.Analysis.JointRealC1
import HolomorphicAnosov.Analysis.Flow.ExistsRealC1PartialFlow

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology NNReal

namespace RealC1FlowExistence
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A C¹ real field on its original OPEN finite-dimensional domain admits an actual jointly
REAL C¹ local flow on one fixed open rectangle. Picard existence, first-variation defects,
linear-IVP stability, and the product-partial criterion are all kernel checked. The derivative
is explicit: `(h,τ) ↦ Y(x,t)h + τ • F(Φ(x,t))`. The range stays in the original field domain.
No completeness of the field, spatial differentiability of Picard iterates, global flow,
group law, or inverse is assumed. Higher regularity is a separate component. -/
theorem exists_real_c1_local_flow [FiniteDimensional ℝ E]
    (F : E → E) (Ω : Set E) (hΩ : IsOpen Ω) (hF : ContDiffOn ℝ 1 F Ω)
    (x₀ : E) (hx₀ : x₀ ∈ Ω) :
    ∃ r > 0, ∃ S > 0, ∃ Φ : E × ℝ → E, ∃ Y : E × ℝ → E →L[ℝ] E,
      ContDiffOn ℝ 1 Φ (ball x₀ r ×ˢ Ioo (-S) S) ∧
      ContinuousOn Y (ball x₀ r ×ˢ Ioo (-S) S) ∧
      (∀ z ∈ ball x₀ r, Φ (z, 0) = z) ∧
      (∀ p ∈ ball x₀ r ×ˢ Ioo (-S) S, Φ p ∈ Ω) ∧
      (∀ p ∈ ball x₀ r ×ˢ Ioo (-S) S,
        HasDerivAt (fun t ↦ Φ (p.1, t)) (F (Φ p)) p.2) ∧
      (∀ p ∈ ball x₀ r ×ˢ Ioo (-S) S,
        HasFDerivAt Φ ((Y p).coprod (ContinuousLinearMap.toSpanSingleton ℝ (F (Φ p)))) p) ∧
      (∀ p ∈ ball x₀ r ×ˢ Ioo (-S) S, ∀ h : E, ∀ τ : ℝ,
        fderiv ℝ Φ p (h, τ) = Y p h + τ • F (Φ p)) := by
  obtain ⟨r, hr, S, hS, α, Y, hc, hmem, hinit, htime, hspace, hY⟩ :=
    exists_real_c1_partial_flow F Ω hΩ hF x₀ hx₀
  have hv : ContinuousOn (fun p : E × ℝ ↦ F (α p.1 p.2))
      (ball x₀ r ×ˢ Ioo (-S) S) :=
    hF.continuousOn.comp hc (fun p hp ↦ hmem p.1 hp.1 p.2 hp.2)
  have hd := HolomorphicAnosov.JointRealC1Scratch.joint_hasFDerivAt_of_partials
    α Y (fun x t ↦ F (α x t)) (ball x₀ r) (Ioo (-S) S)
    isOpen_ball isOpen_Ioo hspace htime hY hv
  have hC1 := HolomorphicAnosov.JointRealC1Scratch.joint_contDiffOn_one_of_partials
    α Y (fun x t ↦ F (α x t)) (ball x₀ r) (Ioo (-S) S)
    isOpen_ball isOpen_Ioo hspace htime hY hv
  refine ⟨r, hr, S, hS, (fun p ↦ α p.1 p.2), (fun p ↦ Y p.1 p.2), hC1, hY,
    hinit, (fun p hp ↦ hmem p.1 hp.1 p.2 hp.2),
    (fun p hp ↦ htime p.1 hp.1 p.2 hp.2), hd, ?_⟩
  intro p hp h τ
  rw [(hd p hp).fderiv]
  rfl

end RealC1FlowExistence
