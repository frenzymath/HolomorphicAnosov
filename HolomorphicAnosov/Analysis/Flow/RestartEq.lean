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
import HolomorphicAnosov.Analysis.Flow.RealFlowEqOn

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology _root_.Topology NNReal

namespace HolomorphicAnosov.W07FiniteFlowContinuation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- Restart a genuine supplied local family inside the original open field domain.
The reference family is compared on the actual intersection of its old interval and the
translated local interval. Source: Teschl Theorem6.1, pp.189–190 and IVP uniqueness. -/
theorem restart_eq
    {F : E → E} {Ω : Set E} (hΩ : IsOpen Ω) (hF : ContDiffOn ℝ 1 F Ω)
    {U : Set P} {J : Set ℝ} (hJ : OrdConnected J) {α : P × ℝ → E}
    (hα : ∀ w ∈ U, ∀ r ∈ J, HasDerivAt (fun t ↦ α (w, t)) (F (α (w, r))) r)
    (hαΩ : ∀ w ∈ U, ∀ r ∈ J, α (w, r) ∈ Ω)
    {A : Set E} {δ : ℝ} {Ψ : E × ℝ → E} (hδ : 0 < δ)
    (hzero : ∀ w ∈ A, Ψ (w, 0) = w)
    (hcurve : ∀ w ∈ A, ∀ r ∈ Ioo (-δ) δ,
      HasDerivAt (fun t ↦ Ψ (w, t)) (F (Ψ (w, r))) r)
    (hΨΩ : ∀ w ∈ A, ∀ r ∈ Ioo (-δ) δ, Ψ (w, r) ∈ Ω)
    {w : P} (hw : w ∈ U) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J)
    (hq : α (w, s) ∈ A) (hdt : t - s ∈ Ioo (-δ) δ) :
    Ψ (α (w, s), t - s) = α (w, t) := by
  let D := J ∩ Ioo (s - δ) (s + δ)
  have hDs : s ∈ D := ⟨hs, by constructor <;> linarith⟩
  have hDt : t ∈ D := ⟨ht, by constructor <;> linarith [hdt.1, hdt.2]⟩
  have hd (r : ℝ) (hr : r ∈ D) :
      HasDerivAt (fun t ↦ Ψ (α (w, s), t - s))
        (F (Ψ (α (w, s), r - s))) r := by
    have hrr : r - s ∈ Ioo (-δ) δ := by constructor <;> linarith [hr.2.1, hr.2.2]
    simpa only [Function.comp_def, id_eq, one_smul] using
      (hcurve (α (w, s)) hq (r - s) hrr).scomp r ((hasDerivAt_id r).sub_const s)
  have heq := RealFlowUniqueness.eqOn_of_contDiffOn hΩ hF (hJ.inter ordConnected_Ioo)
    (fun r hr ↦ (hd r hr).continuousAt.continuousWithinAt)
    (fun r hr ↦ (hα w hw r hr.1).continuousAt.continuousWithinAt)
    (fun r hr ↦ (hd r hr).hasDerivWithinAt)
    (fun r hr ↦ (hα w hw r hr.1).hasDerivWithinAt)
    (fun r hr ↦ hΨΩ _ hq _ (by constructor <;> linarith [hr.2.1, hr.2.2]))
    (fun r hr ↦ hαΩ w hw r hr.1) hDs
    (by simpa only [sub_self] using hzero (α (w, s)) hq)
  exact heq hDt

end HolomorphicAnosov.W07FiniteFlowContinuation
