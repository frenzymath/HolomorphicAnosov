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

omit [FiniteDimensional ℝ E] [BoundarylessManifold I N] [T2Space N]
  [IsManifold I ∞ N] in
/-- A fixed-time slice is smooth on the original initial set. -/
theorem time_slice_smooth
    {U : Set N} {δ : ℝ} {Ψ : N × ℝ → N}
    (hΨ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ Ψ (U ×ˢ Ioo (-δ) δ))
    {t : ℝ} (ht : t ∈ Ioo (-δ) δ) :
    ContMDiffOn I I ∞ (fun y ↦ Ψ (y, t)) U := by
  exact hΨ.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn
    (fun y hy ↦ ⟨hy, ht⟩)

end HolomorphicAnosov.SmoothLocalFlowProof
