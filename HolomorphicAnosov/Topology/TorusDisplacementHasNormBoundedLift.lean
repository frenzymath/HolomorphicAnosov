import HolomorphicAnosov.Paper.Zhang.IntegralToralMap
import Mathlib.Analysis.Normed.Group.AddCircle

namespace HolomorphicAnosov

/-- Choose actual real representatives of a torus displacement without increasing
its finite-product norm. Source: Manning's target canonical-coordinate argument,
Lemma 6, pp.427–428. Choose coordinate representatives, subtract the nearest integer,
use the exact UnitAddCircle norm formula, and combine the coordinate bounds. -/
theorem torus_displacement_has_norm_bounded_lift
    {n : ℕ} (x : UnitAddTorus (Fin n)) :
    ∃ v : Fin n → ℝ, (∀ i, (v i : UnitAddCircle) = x i) ∧ ‖v‖ ≤ ‖x‖ := by
  classical
  let w : Fin n → ℝ := fun i ↦ (AddCircle.equivIco (1 : ℝ) 0 (x i)).val
  have hw : ∀ i, (w i : UnitAddCircle) = x i := fun i ↦ AddCircle.coe_equivIco
  let v : Fin n → ℝ := fun i ↦ w i - (round (w i) : ℝ)
  have hv : ∀ i, (v i : UnitAddCircle) = x i := by
    intro i
    have hi : ((round (w i) : ℝ) : UnitAddCircle) = 0 := by
      apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
      exact ⟨round (w i), by simp only [zsmul_eq_mul, mul_one]⟩
    change ((w i - (round (w i) : ℝ) : ℝ) : UnitAddCircle) = x i
    rw [AddCircle.coe_sub, hi, sub_zero, hw]
  refine ⟨v, hv, (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr ?_⟩
  intro i
  have hnorm : ‖v i‖ = ‖x i‖ := by
    rw [← hw i, UnitAddCircle.norm_eq]
    exact Real.norm_eq_abs _
  rw [hnorm]
  exact norm_le_pi_norm x i

end HolomorphicAnosov
