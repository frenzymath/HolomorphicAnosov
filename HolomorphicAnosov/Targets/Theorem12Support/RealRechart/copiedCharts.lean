import HolomorphicAnosov.Targets.Theorem12Support.RealRechart
import HolomorphicAnosov.Targets.Theorem12Support.RealRechart.Recharted
import HolomorphicAnosov.Targets.Theorem12Support.RealRechart.coordinates
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! The recharted type copy carries the atlas obtained by postcomposing the complex charts with a
real continuous linear equivalence. (Zhang, §3, p. 11) -/

namespace HolomorphicAnosov.Theorem12SupportW2

universe u

/-- The atlas on `Recharted X` obtained by postcomposing the charts of `X` with `B`. (Zhang, §3, p.
11) -/
@[instance_reducible]
noncomputable def copiedCharts {d n : ℕ} (X : Type u) [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X]
    (B : ComplexModel d ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (Recharted X) :=
  rechart X B

end HolomorphicAnosov.Theorem12SupportW2



namespace HolomorphicAnosov.Theorem12SupportW2
open scoped ContDiff
variable {d n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
  (B : ComplexModel d ≃L[ℝ] EuclideanSpace ℝ (Fin n))


example (x : X) :
    ((copiedCharts X B).chartAt x).source = (chartAt (ComplexModel d) x).source := rfl



example (x : X) :
    Set.EqOn (fun z ↦ (copiedCharts X B).chartAt x ((chartAt (ComplexModel d) x).symm z))
      B (chartAt (ComplexModel d) x).target := by
  intro z hz
  change B ((chartAt (ComplexModel d) x) ((chartAt (ComplexModel d) x).symm z)) = B z
  rw [OpenPartialHomeomorph.right_inv _ hz]


example (x : X) :
    ContDiffOn ℝ ∞
      (fun z ↦ (copiedCharts X B).chartAt x ((chartAt (ComplexModel d) x).symm z))
      (chartAt (ComplexModel d) x).target := by
  apply B.contDiff.contDiffOn.congr
  intro z hz
  change B ((chartAt (ComplexModel d) x) ((chartAt (ComplexModel d) x).symm z)) = B z
  rw [OpenPartialHomeomorph.right_inv _ hz]


example (x y : X) (z : EuclideanSpace ℝ (Fin n)) :
    (copiedCharts X B).chartAt y (((copiedCharts X B).chartAt x).symm z) =
      B ((chartAt (ComplexModel d) y) ((chartAt (ComplexModel d) x).symm (B.symm z))) := rfl


example (z : ComplexModel 0) : coordinates 0 z = 0 := by
  ext i
  exact Fin.elim0 i


example [IsEmpty X] : Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin n)) (Recharted X)) :=
  ⟨copiedCharts X B⟩

end HolomorphicAnosov.Theorem12SupportW2
