import HolomorphicAnosov.Geometry.SmoothAffineConnection.Basic
import HolomorphicAnosov.Geometry.SmoothOpenInclusionDifferentialInvertible
import Mathlib.Geometry.Manifold.VectorField.LieBracket

/-!
# Canonical restriction of a smooth tangent field to an open subset


-/ 

open Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section

/-- Pulling a smooth field back through an open inclusion gives the canonical restricted field. Its inclusion pushforward is the original field. -/
theorem LocalSmoothVectorField.openRestriction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {U V : Opens M} (hVU : V ≤ U)
    (XU : LocalSmoothVectorField E M U)
    (hinc : ∀ p : V, (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Opens.inclusion hVU) p).IsInvertible) :
    ∃ XV : LocalSmoothVectorField E M V,
      LocalSmoothVectorField.IsRestriction hVU XU XV := by
  let inc : V → U := Opens.inclusion hVU
  let XV : LocalSmoothVectorField E M V :=
    ⟨fun p ↦ VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) inc (fun q ↦ XU q) p,
      fun p ↦ ContMDiffAt.mpullback_vectorField_preimage (m := ∞) (n := ∞)
        (XU.contMDiff (inc p)) (contMDiff_inclusion hVU |>.contMDiffAt)
        (hinc p) (by simp)⟩
  refine ⟨XV, ?_⟩
  intro p
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) inc p
      ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) inc p).inverse (XU (inc p))) = XU (inc p)
  exact (hinc p).self_apply_inverse _

end
end HolomorphicAnosov

