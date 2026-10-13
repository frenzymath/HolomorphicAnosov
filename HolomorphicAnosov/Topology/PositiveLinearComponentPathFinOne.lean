import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Basic.Sign.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp

noncomputable section
namespace HolomorphicAnosov

/-- In dimension one, positive determinant gives the positive scalar path.

Source: Hatcher, *Vector Bundles and K-Theory* (2017), §1.2, pp. 23--24;
the one-dimensional determinant is the unique scalar coefficient.
-/
theorem exists_positive_linear_equiv_injective_path_fin_one
    (L : EuclideanSpace ℝ (Fin 1) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 1))
    (hdet : 0 < LinearMap.det L.toLinearMap) :
    ∃ D : unitInterval → EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1),
      Continuous D ∧ (∀ t, Function.Injective (D t)) ∧
      D 0 = L.toContinuousLinearEquiv.toContinuousLinearMap ∧
      D 1 = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)) := by
  let r : Fin 1 → ℝ := fun _ => (L (EuclideanSpace.single 0 (1 : ℝ))) 0
  have hdet' : LinearMap.det L.toLinearMap = r 0 := by
    rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis]
    rw [Matrix.det_fin_one]
    simp [LinearMap.toMatrix_apply, r]
  have hr0 : 0 < r 0 := by simpa [hdet'] using hdet
  have hr : ∀ i, 0 < r i := by
    intro i
    fin_cases i
    exact hr0
  have hL : ∀ (x : EuclideanSpace ℝ (Fin 1)) i, L x i = r i * x i := by
    intro x i
    fin_cases i
    have hx : x = x 0 • EuclideanSpace.single 0 (1 : ℝ) := by
      ext j
      fin_cases j
      simp
    rw [hx, map_smul]
    simp [r]
    ring
  let E := EuclideanSpace ℝ (Fin 1)
  let D : unitInterval → E →L[ℝ] E := fun t ↦
    (1 - (t : ℝ)) • L.toContinuousLinearEquiv.toContinuousLinearMap +
      (t : ℝ) • ContinuousLinearMap.id ℝ E
  refine ⟨D, by dsimp [D]; fun_prop, ?_, ?_, ?_⟩
  · intro t
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    ext i
    have hi := congrArg (fun v : E ↦ v i) hx
    change (1 - (t : ℝ)) * L x i + (t : ℝ) * x i = 0 at hi
    rw [hL] at hi
    have ha : 0 < (1 - (t : ℝ)) * r i + t := by
      have ht0 : 0 ≤ (t : ℝ) := t.property.1
      have ht1 : (t : ℝ) ≤ 1 := t.property.2
      by_cases ht : (t : ℝ) = 1
      · simp [ht]
      · exact add_pos_of_pos_of_nonneg
          (mul_pos (sub_pos.mpr (lt_of_le_of_ne ht1 ht)) (hr i)) ht0
    change x i = 0
    apply (mul_eq_zero.mp (show ((1 - (t : ℝ)) * r i + t) * x i = 0 by
      nlinarith [hi])).resolve_left ha.ne'
  · apply ContinuousLinearMap.ext
    intro x
    simp [D]
  · apply ContinuousLinearMap.ext
    intro x
    simp [D]
    rw [ContinuousLinearMap.id_apply]

end HolomorphicAnosov
