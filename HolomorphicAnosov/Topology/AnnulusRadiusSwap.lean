import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.GroupWithZero

namespace HolomorphicAnosov.Topology

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- The closed annulus of radii one and two admits an involutive homeomorphism
exchanging the two boundary spheres. Its radius at x is 3 minus the radius of x.

This elementary agent-written formula supplies the boundary-label correction
in the Gallier--Xu/Cairns annulus construction. Set F(x) = ((3-‖x‖)/‖x‖) • x.
On the annulus the denominator and numerator are positive, so the norm is
3-‖x‖. Substituting that equality a second time proves F(F(x))=x. Division
away from zero and scalar multiplication prove continuity, giving the asserted
homeomorphism. This formula is an expansion of the construction, not a quoted
lemma from Cairns preliminary 2(B). -/
theorem annulus_radius_swap :
    ∃ F : {x : Plane | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} ≃ₜ {x : Plane | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2},
      (∀ x, ‖(F x : Plane)‖ = 3 - ‖(x : Plane)‖) ∧
      (∀ x, F (F x) = x) := by
  let A := {x : Plane | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2}
  let f : A → A := fun z ↦
    ⟨((3 - ‖(z : Plane)‖) / ‖(z : Plane)‖) • (z : Plane), by
      have hz : 0 < ‖(z : Plane)‖ := lt_of_lt_of_le (by norm_num) z.property.1
      have hnum : 0 ≤ 3 - ‖(z : Plane)‖ := by linarith [z.property.2]
      have hs : 0 ≤ (3 - ‖(z : Plane)‖) / ‖(z : Plane)‖ := div_nonneg hnum hz.le
      have hn : ‖((3 - ‖(z : Plane)‖) / ‖(z : Plane)‖) • (z : Plane)‖ =
          3 - ‖(z : Plane)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
        field_simp
      change 1 ≤ ‖((3 - ‖(z : Plane)‖) / ‖(z : Plane)‖) • (z : Plane)‖ ∧
        ‖((3 - ‖(z : Plane)‖) / ‖(z : Plane)‖) • (z : Plane)‖ ≤ 2
      rw [hn]
      constructor <;> linarith [z.property.1, z.property.2]⟩
  have hfcont : Continuous f := by
    apply Continuous.subtype_mk
    have hnorm : Continuous fun z : A ↦ ‖(z : Plane)‖ :=
      continuous_norm.comp continuous_subtype_val
    have hden : ∀ z : A, ‖(z : Plane)‖ ≠ 0 :=
      fun z ↦ ne_of_gt (lt_of_lt_of_le (by norm_num) z.property.1)
    have hfrac : Continuous (fun z : A ↦ (3 - ‖(z : Plane)‖) / ‖(z : Plane)‖) := by
      exact (continuous_const.sub hnorm).div hnorm hden
    exact hfrac.smul continuous_subtype_val
  have hfinv (z : A) : f (f z) = z := by
    apply Subtype.ext
    have hz : 0 < ‖(z : Plane)‖ := lt_of_lt_of_le (by norm_num) z.property.1
    have hnum : 0 ≤ 3 - ‖(z : Plane)‖ := by linarith [z.property.2]
    have hs : 0 ≤ (3 - ‖(z : Plane)‖) / ‖(z : Plane)‖ := div_nonneg hnum hz.le
    have hn : ‖(f z : Plane)‖ = 3 - ‖(z : Plane)‖ := by
      change ‖((3 - ‖(z : Plane)‖) / ‖(z : Plane)‖) • (z : Plane)‖ = _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
      field_simp
    change ((3 - ‖(f z : Plane)‖) / ‖(f z : Plane)‖) • (f z : Plane) = z
    rw [hn]
    change ((3 - (3 - ‖(z : Plane)‖)) / (3 - ‖(z : Plane)‖)) •
      (((3 - ‖(z : Plane)‖) / ‖(z : Plane)‖) • (z : Plane)) = z
    rw [show 3 - (3 - ‖(z : Plane)‖) = ‖(z : Plane)‖ by ring]
    have hthree : 3 - ‖(z : Plane)‖ ≠ 0 := by linarith [z.property.2]
    rw [smul_smul]
    field_simp [hthree, ne_of_gt hz]
    simp
  let F : A ≃ₜ A :=
    { toFun := f
      invFun := f
      left_inv := hfinv
      right_inv := hfinv
      continuous_toFun := hfcont
      continuous_invFun := hfcont }
  refine ⟨F, ?_, hfinv⟩
  intro x
  change ‖((3 - ‖(x : Plane)‖) / ‖(x : Plane)‖) • (x : Plane)‖ = _
  have hx : 0 < ‖(x : Plane)‖ := lt_of_lt_of_le (by norm_num) x.property.1
  have hnum : 0 ≤ 3 - ‖(x : Plane)‖ := by linarith [x.property.2]
  have hs : 0 ≤ (3 - ‖(x : Plane)‖) / ‖(x : Plane)‖ := div_nonneg hnum hx.le
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
  field_simp

end HolomorphicAnosov.Topology

