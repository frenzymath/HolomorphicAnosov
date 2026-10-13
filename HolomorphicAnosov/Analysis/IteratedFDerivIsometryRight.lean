import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace HolomorphicAnosov

/-- Right composition by a linear isometric equivalence preserves differences of jets.
Apply Mathlib's exact formula on the whole space; multilinear precomposition
is a linear isometric equivalence and therefore preserves difference norms. -/
theorem norm_iteratedFDeriv_sub_comp_right
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (e : G ≃ₗᵢ[ℝ] E) (f : E → F) (n : ℕ) (x y : G) :
    ‖iteratedFDeriv ℝ n (f ∘ e) x - iteratedFDeriv ℝ n (f ∘ e) y‖ =
      ‖iteratedFDeriv ℝ n f (e x) - iteratedFDeriv ℝ n f (e y)‖ := by
  change ‖iteratedFDeriv ℝ n (f ∘ e.toContinuousLinearEquiv) x -
    iteratedFDeriv ℝ n (f ∘ e.toContinuousLinearEquiv) y‖ = _
  simp only [← iteratedFDerivWithin_univ]
  have hx := e.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (x := x)
      (Set.mem_univ _) n
  have hy := e.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (x := y)
      (Set.mem_univ _) n
  simp only [Set.preimage_univ] at hx hy
  rw [hx, hy]
  change ‖(ContinuousLinearEquiv.continuousMultilinearMapCongrLeft _
      (fun _ : Fin n ↦ e.toContinuousLinearEquiv)) _ -
    (ContinuousLinearEquiv.continuousMultilinearMapCongrLeft _
      (fun _ : Fin n ↦ e.toContinuousLinearEquiv)) _‖ = _
  rw [← map_sub]
  exact ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv _ (fun _ ↦ e)

end HolomorphicAnosov
