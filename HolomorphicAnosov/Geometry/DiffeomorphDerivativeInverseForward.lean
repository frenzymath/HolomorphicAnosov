import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Diffeomorph

noncomputable section
namespace HolomorphicAnosov
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X]

/-- The derivative of the inverse of a diffeomorphism composed with its derivative is the identity
on the tangent space. -/
theorem derivative_inverse_forward (g : Diffeomorph I I X X ∞) (x : X)
    (v : TangentSpace I x) :
    mfderiv I I g.symm (g x) (mfderiv I I g x v) = v := by
  have hc : (g.symm : X → X) ∘ (g : X → X) = id := by
    funext y
    exact g.symm_apply_apply y
  have hd := mfderiv_comp x
    (g.symm.contMDiff.mdifferentiableAt (by simp))
    (g.contMDiff.mdifferentiableAt (by simp))
  rw [hc, mfderiv_id, g.symm_apply_apply] at hd
  exact (congrArg (fun L ↦ L v) hd).symm

end HolomorphicAnosov
