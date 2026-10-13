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
import HolomorphicAnosov.Analysis.Flow.UniquenessOnOrdConnected

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology _root_.Topology NNReal

namespace HolomorphicAnosov.SmoothLocalFlowProof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N] [BoundarylessManifold I N] [T2Space N]
  {V : (x : N) → TangentSpace I x}

omit [FiniteDimensional ℝ E] in
/-- Andrews §6.5: equality at an actual endpoint forces equality of the
original initial points. No endpoint membership in the initial set is used. -/
theorem time_slice_injective
    (hV : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, V x⟩ : TangentBundle I N)))
    {U : Set N} {δ : ℝ} {Ψ : N × ℝ → N} (hδ : 0 < δ)
    (hzero : ∀ y ∈ U, Ψ (y, 0) = y)
    (hcurve : ∀ y ∈ U,
      IsMIntegralCurveOn (I := I) (fun t ↦ Ψ (y, t)) V (Ioo (-δ) δ))
    {t : ℝ} (ht : t ∈ Ioo (-δ) δ) :
    InjOn (fun y ↦ Ψ (y, t)) U := by
  intro x hx y hy heq
  have h := uniqueness_on_ordConnected hV ordConnected_Ioo
    (hcurve x hx) (hcurve y hy) ht heq
  simpa only [hzero x hx, hzero y hy] using h ⟨neg_lt_zero.mpr hδ, hδ⟩

end HolomorphicAnosov.SmoothLocalFlowProof
