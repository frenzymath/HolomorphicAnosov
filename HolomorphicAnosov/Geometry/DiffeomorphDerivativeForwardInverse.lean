import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Diffeomorph

noncomputable section
namespace HolomorphicAnosov
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X]

/-- The derivative of a diffeomorphism composed with the derivative of its inverse is the identity
on the tangent space. -/
theorem derivative_forward_inverse (g : Diffeomorph I I X X ∞) (x : X)
    (v : TangentSpace I x) :
    mfderiv I I g (g.symm x) (mfderiv I I g.symm x v) = v := by
  have hc : (g : X → X) ∘ (g.symm : X → X) = id := by
    funext y
    exact g.apply_symm_apply y
  have hd := mfderiv_comp x
    (g.contMDiff.mdifferentiableAt (by simp))
    (g.symm.contMDiff.mdifferentiableAt (by simp))
  rw [hc, mfderiv_id, g.apply_symm_apply] at hd
  exact (congrArg (fun L ↦ L v) hd).symm

end HolomorphicAnosov
