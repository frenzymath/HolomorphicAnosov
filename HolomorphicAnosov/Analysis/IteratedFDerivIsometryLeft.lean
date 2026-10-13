import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace HolomorphicAnosov

/-- Left composition by a linear isometric equivalence preserves differences of jets.
This follows from Mathlib's exact derivative composition formula, linearity of
postcomposition, and invariance of the multilinear operator norm. -/
theorem norm_iteratedFDeriv_sub_comp_left
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (e : F ≃ₗᵢ[ℝ] G) (f : E → F) (n : ℕ) (x y : E) :
    ‖iteratedFDeriv ℝ n (e ∘ f) x - iteratedFDeriv ℝ n (e ∘ f) y‖ =
      ‖iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n f y‖ := by
  change ‖iteratedFDeriv ℝ n (e.toContinuousLinearEquiv ∘ f) x -
    iteratedFDeriv ℝ n (e.toContinuousLinearEquiv ∘ f) y‖ = _
  have hx := e.toContinuousLinearEquiv.iteratedFDeriv_comp_left (f := f) (x := x) (i := n)
  have hy := e.toContinuousLinearEquiv.iteratedFDeriv_comp_left (f := f) (x := y) (i := n)
  rw [hx, hy]
  change ‖e.toContinuousLinearEquiv.continuousMultilinearMapCongrRight (fun _ : Fin n ↦ E) _ -
    e.toContinuousLinearEquiv.continuousMultilinearMapCongrRight (fun _ : Fin n ↦ E) _‖ = _
  rw [← map_sub]
  exact e.toLinearIsometry.norm_compContinuousMultilinearMap _

end HolomorphicAnosov
