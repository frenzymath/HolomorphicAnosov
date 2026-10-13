import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.MaximalAtlasRestriction
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
/-- Derivatives of restricted chart maps identify the coordinate vectors of restricted fields. (Andrews, §8.3) -/
theorem chartVector_isRestriction {U V : Opens M} (hUV : U ≤ V)
    (hU : Nonempty U) (hV : Nonempty V)
    (c : OpenPartialHomeomorph M E) (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    (X : LocalSmoothVectorField E M V) (Y : LocalSmoothVectorField E M U)
    (hXY : LocalSmoothVectorField.IsRestriction hUV X Y)
    (p : U) (hp : (p : M) ∈ c.source) :
    mvfderiv 𝓘(ℝ, E) (c.subtypeRestr hU) p (Y p) =
      mvfderiv 𝓘(ℝ, E) (c.subtypeRestr hV) (Opens.inclusion hUV p)
        (X (Opens.inclusion hUV p)) := by
  have hpV : Opens.inclusion hUV p ∈ (c.subtypeRestr hV).source := by
    simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hp
  have hd := mfderiv_comp p
    ((contMDiffAt_of_mem_maximalAtlas
      (HolomorphicAnosov.maximalAtlas_subtypeRestr c hc V hV) hpV).mdifferentiableAt (by simp))
    ((contMDiff_inclusion (I := 𝓘(ℝ, E)) (n := ∞) hUV p).mdifferentiableAt (by simp))
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
      ((c.subtypeRestr hV) ∘ Opens.inclusion hUV) p (Y p) = _
  rw [hd, ContinuousLinearMap.comp_apply, hXY p]
  rfl

end ConnectionChristoffelLocal
end
end HolomorphicAnosov
