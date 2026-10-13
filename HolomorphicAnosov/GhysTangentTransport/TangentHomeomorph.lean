import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousRealTangentSubbundle
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Diffeomorph
import HolomorphicAnosov.GhysTangentTransport.DerivativeLeftInverse

open scoped ContDiff Manifold Topology _root_.Topology
namespace HolomorphicAnosov.GhysTangentTransport
noncomputable section
universe u v
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H K : Type*} [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace K N]
  [IsManifold I ∞ M] [IsManifold J ∞ N]
  (e : Diffeomorph I J M N ∞)

/-- The derivative of a diffeomorphism defines a homeomorphism of tangent bundles, with inverse given by the derivative of the inverse map. -/
def tangentHomeomorph : TangentBundle I M ≃ₜ TangentBundle J N where
  toFun := tangentMap I J e
  invFun := tangentMap J I e.symm
  left_inv := by
    rintro ⟨x, v⟩
    dsimp [tangentMap]
    apply Bundle.TotalSpace.ext
    · exact e.symm_apply_apply x
    · exact heq_of_eq (derivative_leftInverse e x v)
  right_inv := by
    rintro ⟨y, v⟩
    dsimp [tangentMap]
    apply Bundle.TotalSpace.ext
    · exact e.apply_symm_apply y
    · exact heq_of_eq (derivative_leftInverse e.symm y v)
  continuous_toFun := e.contMDiff.continuous_tangentMap (by simp)
  continuous_invFun := e.symm.contMDiff.continuous_tangentMap (by simp)


end
end HolomorphicAnosov.GhysTangentTransport
