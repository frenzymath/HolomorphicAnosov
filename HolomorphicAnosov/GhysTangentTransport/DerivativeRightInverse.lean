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
/-- The derivatives of the forward and inverse maps compose to the identity on each receiving fibre. -/
theorem derivative_rightInverse (x : M) :
    Function.RightInverse (mfderiv J I e.symm (e x)) (mfderiv I J e x) := by
  intro w
  have hc := mfderiv_comp (e x)
    (e.contMDiff.mdifferentiable (by simp) (e.symm (e x)))
    (e.symm.contMDiff.mdifferentiable (by simp) (e x))
  have hmap : (e : M → N) ∘ (e.symm : N → M) = id := by
    funext y; exact e.apply_symm_apply y
  rw [hmap, mfderiv_id] at hc
  have hcw := congrArg (fun T ↦ T w) hc
  change w = (mfderiv I J e (e.symm (e x))) ((mfderiv J I e.symm (e x)) w) at hcw
  rw [e.symm_apply_apply] at hcw
  exact hcw.symm


end
end HolomorphicAnosov.GhysTangentTransport
