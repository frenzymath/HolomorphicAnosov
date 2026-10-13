import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.InclusionDerivative
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
/-- This is the restriction of a smooth tangent field to an open submanifold. (Andrews, §8.3) -/
def restrictField {U V : Opens M} (hUV : U ≤ V) (X : LocalSmoothVectorField E M V) :
    LocalSmoothVectorField E M U := by
  let : IsManifold 𝓘(ℝ, E) 2 V := IsManifold.of_le (n := ∞) (by simp)
  let : IsManifold 𝓘(ℝ, E) 2 U := IsManifold.of_le (n := ∞) (by simp)
  exact ⟨VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (Opens.inclusion hUV) X,
    X.contMDiff.mpullback_vectorField
      (contMDiff_inclusion (I := 𝓘(ℝ, E)) (n := ∞) hUV)
      (inclusion_mfderiv_isInvertible hUV) (by simp)⟩

end ConnectionChristoffelLocal
end
end HolomorphicAnosov
