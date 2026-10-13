import HolomorphicAnosov.Geometry.HermitianMetricVolumeDefinitions
import Mathlib.Analysis.Calculus.ContDiff.Operations

open scoped ContDiff

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]

set_option backward.isDefEq.respectTransparency false in
/-- Smooth metric coefficients have a smooth determinant density, by the finite permutation expansion. (Demailly, VI §4.) -/
theorem hermitian_chart_density_smooth [IsManifold (complexModel d) ∞ X]
    (h : HermitianTangentMetricCore d X) (hh : IsSmoothHermitianTangentMetric h)
    (e : OpenPartialHomeomorph X (ComplexModel d))
    (he : e ∈ IsManifold.maximalAtlas (complexModel d) ∞ X) :
    ContDiffOn ℝ ∞ (hermitianMetricChartVolumeDensity h e) e.target := by
  have hdet : ContDiffOn ℝ ∞
      (fun z ↦ Matrix.det fun i j ↦ hermitianTangentChartCoefficient h e i j z) e.target := by
    simp only [Matrix.det_apply']
    apply ContDiffOn.sum
    intro σ hσ
    exact contDiffOn_const.mul (contDiffOn_prod (fun i hi ↦ hh e he _ _))
  exact Complex.reCLM.contDiff.comp_contDiffOn hdet

end HolomorphicAnosov

