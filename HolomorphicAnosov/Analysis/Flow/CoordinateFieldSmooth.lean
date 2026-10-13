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

namespace HolomorphicAnosov.W07ManifoldFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N] [BoundarylessManifold I N] [T2Space N]
  {V : (x : N) → TangentSpace I x}

omit [FiniteDimensional ℝ E] [BoundarylessManifold I N] [T2Space N] in
/-- The original vector field, expressed in one actual tangent-bundle chart, is smooth on
its genuine open coordinate interior. This includes boundaryless manifolds whose model
with corners itself is not boundaryless. Source: Andrews Proposition6.1.2 and Mathlib charts. -/
theorem coordinate_field_smooth
    (hV : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, V x⟩ : TangentBundle I N))) (z : N) :
    let e := extChartAt I z
    let F : E → E := fun q ↦ tangentCoordChange I (e.symm q) z (e.symm q) (V (e.symm q))
    ContDiffOn ℝ ∞ F (interior e.target) := by
  intro e F
  have hs := (contMDiffOn_extChartAt_symm (I := I) z (n := ∞)).mono interior_subset
  have hcomp := hV.comp_contMDiffOn hs
  have hchart : ContMDiffOn I.tangent 𝓘(ℝ, E × E) ∞
      (extChartAt I.tangent (⟨z, V z⟩ : TangentBundle I N))
      (extChartAt I.tangent (⟨z, V z⟩ : TangentBundle I N)).source := by
    simpa only [extChartAt_source] using
      (contMDiffOn_extChartAt (I := I.tangent) (x := (⟨z, V z⟩ : TangentBundle I N))
        (n := ∞))
  have hcoord := hchart.comp hcomp (fun q hq ↦ by
    change (⟨e.symm q, V (e.symm q)⟩ : TangentBundle I N) ∈
      (extChartAt I.tangent (⟨z, V z⟩ : TangentBundle I N)).source
    simp only [extChartAt_source, TangentBundle.mem_chart_source_iff]
    have hh := e.map_target (interior_subset hq)
    change e.symm q ∈ (extChartAt I z).source at hh
    rwa [extChartAt_source] at hh)
  have hh := hcoord.contDiffOn.snd
  exact hh.congr (fun q _ ↦ rfl)

end HolomorphicAnosov.W07ManifoldFlow
