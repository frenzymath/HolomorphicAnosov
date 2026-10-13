import HolomorphicAnosov.Geometry.SmoothAffineConnection
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorField.Pullback
open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
namespace ConnectionChristoffelLocal
/-- The tangent coordinate functions are smooth on a full-source chart. (Andrews, §8.3) -/
theorem fullSource_coordinateVector_contMDiff (U : Opens M)
    (c : OpenPartialHomeomorph U E) (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ U)
    (hsource : c.source = univ) (Y : LocalSmoothVectorField E M U) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun p ↦ mvfderiv 𝓘(ℝ, E) c p (Y p)) := by
  have hcD : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c := by
    have h := contMDiffOn_of_mem_maximalAtlas hc
    rwa [hsource, contMDiffOn_univ] at h
  have ht := hcD.contMDiff_tangentMap (m := ∞) (by simp)
  have hy := ht.comp Y.contMDiff
  exact (contMDiff_snd_tangentBundle_modelSpace E 𝓘(ℝ, E)).comp hy

end ConnectionChristoffelLocal
end
end HolomorphicAnosov
