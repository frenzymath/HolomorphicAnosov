import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Complemented
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import HolomorphicAnosov.Geometry.ComplexModel




/-! This file gives a split normal form for an injective complex-linear map. (Demailly, I.7.15, p. 60).
-/
namespace HolomorphicAnosov

/-- An injective continuous complex-linear map into a finite-dimensional complex space admits a complex complement and a continuous product equivalence sending `(u, 0)` to `A u`. (Demailly, I.7.15, p. 60). -/
theorem complex_linear_split_normal_form
    {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E']
    (A : E →L[ℂ] E') (hA : Function.Injective A) :
    ∃ F : Submodule ℂ E', ∃ e : (E × F) ≃L[ℂ] E',
      ∀ u : E, e (u, 0) = A u := by
  let := FiniteDimensional.complete ℂ E'
  let := FiniteDimensional.complete ℂ E
  let := FiniteDimensional.complete ℂ (LinearMap.range A.toLinearMap)
  let r : E ≃ₗ[ℂ] LinearMap.range A.toLinearMap :=
    LinearEquiv.ofInjective A.toLinearMap hA
  let rc : E ≃L[ℂ] LinearMap.range A.toLinearMap :=
    r.toContinuousLinearEquivOfContinuous (r.toLinearMap.continuous_of_finiteDimensional)
  obtain ⟨F, hF⟩ := (LinearMap.range A.toLinearMap).exists_isCompl
  let p : (LinearMap.range A.toLinearMap × F) ≃L[ℂ] E' := by
    letI := FiniteDimensional.complete ℂ (LinearMap.range A.toLinearMap × F)
    exact ((LinearMap.range A.toLinearMap).prodEquivOfIsCompl F hF).toContinuousLinearEquivOfContinuous
      (by exact (LinearMap.continuous_of_finiteDimensional _))
  refine ⟨F, rc.prodCongr (ContinuousLinearEquiv.refl ℂ F) |>.trans p, ?_⟩
  intro u
  change p (rc u, 0) = A u
  change (p.toLinearEquiv (rc u, 0) : E') = A u
  simp [p, Submodule.coe_prodEquivOfIsCompl']
  change (r u : E') = A u
  rfl

end HolomorphicAnosov
