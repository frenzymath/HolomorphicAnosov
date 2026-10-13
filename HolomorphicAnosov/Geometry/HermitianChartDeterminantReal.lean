import HolomorphicAnosov.Geometry.HermitianTangentMetric
import Mathlib.LinearAlgebra.Matrix.Hermitian

open scoped ContDiff

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]

/-- Conjugate symmetry makes the chart determinant real even outside its target. (Demailly, VI §4.) -/
theorem hermitian_chart_det_real (h : HermitianTangentMetricCore d X)
    (e : OpenPartialHomeomorph X (ComplexModel d)) (z : ComplexModel d) :
    (Matrix.det fun i j ↦ hermitianTangentChartCoefficient h e i j z).im = 0 := by
  let H : Matrix (Fin d) (Fin d) ℂ := fun i j ↦ hermitianTangentChartCoefficient h e i j z
  have hH : H.IsHermitian := by
    ext i j
    exact (h (e.symm z)).conj_inner_symm _ _
  have hd : star H.det = H.det := by rw [← Matrix.det_conjTranspose, hH]
  have hi := congrArg Complex.im hd
  change -(H.det).im = (H.det).im at hi
  change H.det.im = 0
  linarith


end HolomorphicAnosov
