import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.FunProp

noncomputable section
namespace HolomorphicAnosov

/-- The zero-dimensional positive-component path is the constant identity path.

Source: Hatcher, *Vector Bundles and K-Theory* (2017), §1.2, pp. 23--24;
the zero-dimensional Euclidean space is a subsingleton.
-/
theorem exists_positive_linear_equiv_injective_path_fin_zero
    (L : EuclideanSpace ℝ (Fin 0) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 0)) :
    ∃ D : unitInterval → EuclideanSpace ℝ (Fin 0) →L[ℝ] EuclideanSpace ℝ (Fin 0),
      Continuous D ∧ (∀ t, Function.Injective (D t)) ∧
      D 0 = L.toContinuousLinearEquiv.toContinuousLinearMap ∧
      D 1 = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 0)) := by
  have hL : L = LinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 0)) := Subsingleton.elim _ _
  subst L
  let E := EuclideanSpace ℝ (Fin 0)
  let D : unitInterval → E →L[ℝ] E := fun _ => ContinuousLinearMap.id ℝ E
  refine ⟨D, by dsimp [D]; fun_prop, ?_, ?_, ?_⟩
  · intro t x y h
    exact h
  · rfl
  · rfl

end HolomorphicAnosov
