import HolomorphicAnosov.Geometry.HermitianTangentMetric
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

open scoped ContDiff

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]

set_option backward.isDefEq.respectTransparency false in
/-- The genuine inverse-chart differential sends the coordinate basis to an independent frame. (Demailly, VI §4.) -/
theorem hermitian_chart_frame_independent [IsManifold (complexModel d) ∞ X]
    (e : OpenPartialHomeomorph X (ComplexModel d))
    (he : e ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
    (z : ComplexModel d) (hz : z ∈ e.target) :
    LinearIndependent ℂ (hermitianTangentChartFrame e z) := by
  have heD : e.MDifferentiable (complexModel d) (complexModel d) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩
  unfold hermitianTangentChartFrame
  simpa [Function.comp_def] using
    ((Pi.basisFun ℂ (Fin d)).linearIndependent.map'
    (NormedSpace.fromTangentSpace z).symm.toLinearMap
    (LinearMap.ker_eq_bot.mpr (NormedSpace.fromTangentSpace z).symm.injective)).map'
      (mfderiv (complexModel d) (complexModel d) e.symm z).toLinearMap
      (LinearMap.ker_eq_bot.mpr (heD.symm.mfderiv_injective hz))


end HolomorphicAnosov
