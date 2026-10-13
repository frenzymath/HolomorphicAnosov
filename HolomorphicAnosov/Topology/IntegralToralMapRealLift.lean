import HolomorphicAnosov.Paper.Zhang.IntegralToralMap
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

namespace HolomorphicAnosov

/-- The actual row-coordinate toral map commutes with the coordinate quotient of
its real integer matrix action. Source: Manning Lemma 6, pp.427–428, target canonical
coordinates; this is the native quotient-additive-homomorphism finite-sum calculation.
Rows act on the original column vector, with no transpose or replacement toral map. -/
theorem integral_toral_map_real_lift
    {n : ℕ} (A : Matrix.GeneralLinearGroup (Fin n) ℤ) (v : Fin n → ℝ) :
    integralToralMap A (fun i ↦ (v i : UnitAddCircle)) =
      fun i ↦ ((∑ j : Fin n, (A i j : ℝ) * v j : ℝ) : UnitAddCircle) := by
  funext i
  change (∑ j : Fin n, A i j • (v j : UnitAddCircle)) =
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
      (∑ j : Fin n, (A i j : ℝ) * v j)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change A i j • (v j : UnitAddCircle) = (((A i j : ℝ) * v j : ℝ) : UnitAddCircle)
  rw [← AddCircle.coe_zsmul]
  congr 1
  simp only [zsmul_eq_mul]

end HolomorphicAnosov
