import HolomorphicAnosov.Geometry.ComplexLinearSplitNormalForm

namespace HolomorphicAnosov

/-- An injective complex-linear map between finite-dimensional complex spaces has a continuous complex-linear left inverse. -/
theorem complex_linear_left_inverse_of_injective
    {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E']
    (A : E →L[ℂ] E') (hA : Function.Injective A) :
    ∃ Q : E' →L[ℂ] E, Q.comp A = ContinuousLinearMap.id ℂ E := by
  obtain ⟨F, e, he⟩ := complex_linear_split_normal_form A hA
  let Q : E' →L[ℂ] E :=
    (ContinuousLinearMap.fst ℂ E F).comp e.symm.toContinuousLinearMap
  refine ⟨Q, ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  change (e.symm (A v)).1 = v
  rw [← he v]
  simp

end HolomorphicAnosov
