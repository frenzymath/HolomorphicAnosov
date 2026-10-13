import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.CoordinateVectorSmooth
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
/-- Scalar coefficient functions of a smooth field are differentiable in full-source coordinates. (Andrews, §8.3) -/
theorem fullSource_coordinateCoefficient_differentiableAt (U : Opens M)
    {n : ℕ} (b : Basis (Fin n) ℝ E)
    (c : OpenPartialHomeomorph U E) (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ U)
    (hsource : c.source = univ) (Y : LocalSmoothVectorField E M U)
    (p : U) (k : Fin n) :
    DifferentiableAt ℝ (Y.coordinateCoefficient b c k) (c p) := by
  have hp : p ∈ c.source := by rw [hsource]; trivial
  have hs := contMDiffAt_symm_of_mem_maximalAtlas hc (c.map_source hp)
  have hv := (fullSource_coordinateVector_contMDiff U c hc hsource Y (c.symm (c p))).comp (c p) hs
  have hb := (b.coord k).toContinuousLinearMap.contMDiffAt.comp (c p) hv
  exact hb.contDiffAt.differentiableAt (by simp)

end ConnectionChristoffelLocal
end
end HolomorphicAnosov
