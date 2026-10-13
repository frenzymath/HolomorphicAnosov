import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousRealTangentSubbundle
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Diffeomorph

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

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
/-- The derivatives of the inverse and forward maps compose to the identity on each original fibre. -/
theorem derivative_leftInverse (x : M) :
    Function.LeftInverse (mfderiv J I e.symm (e x)) (mfderiv I J e x) := by
  intro v
  have hc := mfderiv_comp x
    (e.symm.contMDiff.mdifferentiable (by simp) (e x))
    (e.contMDiff.mdifferentiable (by simp) x)
  have hmap : (e.symm : N → M) ∘ (e : M → N) = id := by
    funext y; exact e.symm_apply_apply y
  rw [hmap, mfderiv_id] at hc
  exact (congrArg (fun T ↦ T v) hc).symm


end
end HolomorphicAnosov.GhysTangentTransport
