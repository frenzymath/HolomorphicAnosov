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

omit [T2Space N] in
/-- Andrews 6.1.1: the individual local existence clause follows from native
Picard--Lindelöf in charts; this does not assert smooth initial-point dependence. -/
theorem individual_local_existence
    (hV : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, V x⟩ : TangentBundle I N)))
    (z : N) :
    ∃ (δ : ℝ) (γ : ℝ → N), 0 < δ ∧ γ 0 = z ∧
      IsMIntegralCurveOn (I := I) γ V (Ioo (-δ) δ) := by
  obtain ⟨γ, hγ0, hγ⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless (I := I) 0
      ((hV.of_le (by simp)).contMDiffAt (x := z))
  obtain ⟨δ, hδ, hγ⟩ := isMIntegralCurveAt_iff'.mp hγ
  exact ⟨δ, γ, hδ, hγ0, by simpa [Real.ball_eq_Ioo] using hγ⟩

end HolomorphicAnosov.SmoothLocalFlowProof
