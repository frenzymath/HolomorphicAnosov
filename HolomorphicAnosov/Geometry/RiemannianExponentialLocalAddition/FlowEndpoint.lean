import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime

/-!
Reusable FlowEndpoint declarations from the Riemannian exponential construction.
-/ 

open Set Bundle TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.W07FlowContinuation

open Set Filter
open scoped Manifold ContDiff Topology _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N] [BoundarylessManifold I N] [T2Space N]
  {V : (x : N) → TangentSpace I x}

/-- A smooth trajectory on an actual open interval containing both prescribed times. -/
def Endpoint (V : (x : N) → TangentSpace I x) (t : ℝ) (z q : N) : Prop :=
  ∃ (a b : ℝ) (γ : ℝ → N), 0 ∈ Ioo a b ∧ t ∈ Ioo a b ∧
    ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Ioo a b) ∧ IsMIntegralCurveOn γ V (Ioo a b) ∧
    γ 0 = z ∧ γ t = q

end HolomorphicAnosov.W07FlowContinuation
