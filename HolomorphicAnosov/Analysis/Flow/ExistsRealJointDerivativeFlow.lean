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
import HolomorphicAnosov.Analysis.Flow.ExistsRealC1PartialFlow

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology NNReal

namespace RealC1FlowExistence
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Closed original-open-field existence with the ACTUAL full joint Fréchet derivative.
For every `(x,t)` in the same fixed open rectangle, the derivative maps `(h,τ)` to
`Y(x,t)h + τ • F(Φ(x,t))`. No joint differentiability assumption is introduced. -/
theorem exists_real_joint_derivative_flow [FiniteDimensional ℝ E]
    (F : E → E) (Ω : Set E) (hΩ : IsOpen Ω) (hF : ContDiffOn ℝ 1 F Ω)
    (x₀ : E) (hx₀ : x₀ ∈ Ω) :
    ∃ r > 0, ∃ S > 0, ∃ Φ : E × ℝ → E, ∃ Y : E × ℝ → E →L[ℝ] E,
      ContinuousOn Φ (ball x₀ r ×ˢ Ioo (-S) S) ∧
      ContinuousOn Y (ball x₀ r ×ˢ Ioo (-S) S) ∧
      (∀ z ∈ ball x₀ r, Φ (z, 0) = z) ∧
      (∀ p ∈ ball x₀ r ×ˢ Ioo (-S) S, Φ p ∈ Ω) ∧
      (∀ p ∈ ball x₀ r ×ˢ Ioo (-S) S,
        HasDerivAt (fun t ↦ Φ (p.1, t)) (F (Φ p)) p.2) ∧
      (∀ p ∈ ball x₀ r ×ˢ Ioo (-S) S,
        HasFDerivAt Φ ((Y p).coprod (ContinuousLinearMap.toSpanSingleton ℝ (F (Φ p)))) p) := by
  obtain ⟨r, hr, S, hS, α, Y, hc, hmem, hinit, htime, hspace, hY⟩ :=
    exists_real_c1_partial_flow F Ω hΩ hF x₀ hx₀
  have hFc : ContinuousOn F Ω := hF.continuousOn
  have hv : ContinuousOn (fun p : E × ℝ ↦ F (α p.1 p.2))
      (ball x₀ r ×ˢ Ioo (-S) S) :=
    hFc.comp hc (fun p hp ↦ hmem p.1 hp.1 p.2 hp.2)
  have hd := HolomorphicAnosov.JointRealC1Scratch.joint_hasFDerivAt_of_partials
    α Y (fun x t ↦ F (α x t))
    (ball x₀ r) (Ioo (-S) S) isOpen_ball isOpen_Ioo hspace htime hY hv
  exact ⟨r, hr, S, hS, (fun p ↦ α p.1 p.2), (fun p ↦ Y p.1 p.2), hc, hY,
    hinit, (fun p hp ↦ hmem p.1 hp.1 p.2 hp.2),
    (fun p hp ↦ htime p.1 hp.1 p.2 hp.2), hd⟩

end RealC1FlowExistence
