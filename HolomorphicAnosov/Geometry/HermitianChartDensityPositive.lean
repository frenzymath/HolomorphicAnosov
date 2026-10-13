import HolomorphicAnosov.Geometry.HermitianMetricVolumeDefinitions
import HolomorphicAnosov.Geometry.HermitianChartFrameIndependent
import HolomorphicAnosov.Geometry.HermitianCoreDeterminantPositive

open scoped ContDiff

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]

/-- The actual chart density is strictly positive on a compatible chart's target. (Demailly, VI §4.) -/
theorem hermitian_chart_density_pos [IsManifold (complexModel d) ∞ X]
    (h : HermitianTangentMetricCore d X)
    (e : OpenPartialHomeomorph X (ComplexModel d))
    (he : e ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
    (z : ComplexModel d) (hz : z ∈ e.target) :
    0 < hermitianMetricChartVolumeDensity h e z :=
  hermitian_core_det_pos (h (e.symm z)) (hermitianTangentChartFrame e z)
    (hermitian_chart_frame_independent e he z hz)

end HolomorphicAnosov

