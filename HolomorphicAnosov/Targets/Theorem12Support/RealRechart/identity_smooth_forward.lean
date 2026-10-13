import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import HolomorphicAnosov.Targets.Theorem12Support.RealRechart.coordinates
import HolomorphicAnosov.Targets.Theorem12Support.RealRechart
import HolomorphicAnosov.Targets.Theorem12Support.RealRechart.Recharted
import HolomorphicAnosov.Targets.Theorem12Support.RealRechart.copiedCharts
import HolomorphicAnosov.Targets.Theorem12Support.RealRechart.copyHomeomorph

/-! The identity from the original real charted space to the recharted copy is smooth. (Zhang, §3,
p. 11) -/

open scoped ContDiff Manifold Topology _root_.Topology
open Set
namespace HolomorphicAnosov.Theorem12SupportW2
noncomputable section
universe u

variable {d n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X]
  (B : ComplexModel d ≃L[ℝ] EuclideanSpace ℝ (Fin n))

/-- The identity from `X` with its original real model to `Recharted X` with the atlas postcomposed
by `B` is infinitely differentiable. (Zhang, §3, p. 11) -/

theorem identity_smooth_forward :
    letI := copiedCharts (X := X) B
    ContMDiff (realModel d) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (copyHomeomorph (X := X) : X → Recharted X) := by
  let := copiedCharts (X := X) B
  intro x
  apply contMDiffAt_iff.mpr
  refine ⟨continuous_id.continuousAt, ?_⟩
  have hB := (B.contDiff (n := ∞)).contDiffAt (x := (extChartAt (realModel d) x) x)
  apply (hB.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [extChartAt_target_mem_nhds (I := realModel d) x] with z hz
  change B ((chartAt (ComplexModel d) x) ((chartAt (ComplexModel d) x).symm z)) = B z
  exact congrArg B ((extChartAt (realModel d) x).right_inv hz)

end
end HolomorphicAnosov.Theorem12SupportW2

