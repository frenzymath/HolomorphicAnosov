import HolomorphicAnosov.Targets.Theorem12Support.RealRechart.copiedCharts
import HolomorphicAnosov.Targets.Theorem12Support.RealRechart.copyHomeomorph
import HolomorphicAnosov.Targets.Theorem12Support.RealRechart.Recharted
import Mathlib.Geometry.Manifold.Diffeomorph

/-! The identity from the recharted copy to the original real charted space is smooth. (Zhang, §3,
p. 11) -/

open scoped ContDiff Manifold Topology _root_.Topology
open Set
namespace HolomorphicAnosov.Theorem12SupportW2
noncomputable section
universe u

variable {d n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X]
  (B : ComplexModel d ≃L[ℝ] EuclideanSpace ℝ (Fin n))

/-- The identity from `Recharted X` with the atlas postcomposed by `B` to `X` with its original real
model is infinitely differentiable. (Zhang, §3, p. 11) -/

theorem identity_smooth_backward :
    letI := copiedCharts (X := X) B
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (realModel d) ∞
      ((copyHomeomorph (X := X)).symm : Recharted X → X) := by
  let := copiedCharts (X := X) B
  intro x
  apply contMDiffAt_iff.mpr
  refine ⟨continuous_id.continuousAt, ?_⟩
  have hB := (B.symm.contDiff (n := ∞)).contDiffAt
    (x := (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) x)
  apply (hB.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [extChartAt_target_mem_nhds
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) x] with z hz
  change (chartAt (ComplexModel d) (show X from x))
    ((chartAt (ComplexModel d) (show X from x)).symm (B.symm z)) = B.symm z
  apply (chartAt (ComplexModel d) (show X from x)).right_inv
  have hz' : z ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).target := by
    simpa only [mfld_simps] using hz
  exact hz'

end
end HolomorphicAnosov.Theorem12SupportW2

