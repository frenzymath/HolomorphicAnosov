import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Logic.Equiv.PartialEquiv

/-! Characteristic maps for bounded closed convex bodies. The radial disk extension
implements the simplex characteristic-map construction used in Hatcher,
Algebraic Topology, §2.1 pp.104,107 and Proposition A.2 p.521. -/

namespace HolomorphicAnosov
open Set Metric Topology _root_.Topology Bornology

/-- A bounded closed convex body with nonempty interior admits a globally continuous
characteristic map: its open unit ball is identified with the interior, its closed
unit ball maps onto the body, and its unit sphere maps onto the frontier.

Use the ambient gauge homeomorphism taking interior, body and frontier onto open
ball, closed ball and sphere. Before applying its inverse, retract the whole space
onto the closed unit ball by x ↦ (max 1 ‖x‖)⁻¹ • x. This retraction is continuous,
fixes the closed ball, and has image in it. The gauge homeomorphism is the inverse
on the open ball. The construction also applies to the zero vector space. -/
theorem convex_body_characteristic_map {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}
    (hc : Convex ℝ s) (hne : (interior s).Nonempty) (hb : IsBounded s)
    (hs : IsClosed s) :
    ∃ χ : PartialEquiv E E,
      χ.source = ball 0 1 ∧ χ.target = interior s ∧
      Continuous χ ∧ Continuous χ.symm ∧
      (∀ x, χ x ∈ s) ∧ χ '' closedBall 0 1 = s ∧
      χ '' ball 0 1 = interior s ∧ χ '' sphere 0 1 = frontier s := by
  obtain ⟨h, hi, hd, hf⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hc hne hb
  rw [hs.closure_eq] at hd
  let ρ : E → E := fun x ↦ (max 1 ‖x‖)⁻¹ • x
  have hρcont : Continuous ρ := by
    exact ((continuous_const.max continuous_norm).inv₀
      (fun x ↦ ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖x‖)))).smul
      continuous_id
  have hρfix : ∀ x ∈ closedBall (0 : E) 1, ρ x = x := by
    intro x hx
    have hx' : ‖x‖ ≤ 1 := by simpa using hx
    simp [ρ, max_eq_left hx']
  have hρmem : ∀ x, ρ x ∈ closedBall (0 : E) 1 := by
    intro x
    have hp : 0 < max 1 ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    change dist ((max 1 ‖x‖)⁻¹ • x) 0 ≤ 1
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hp.le)]
    simpa [div_eq_mul_inv, mul_comm] using
      (div_le_one hp).mpr (le_max_right 1 ‖x‖)
  have hi' : ∀ x, h.symm x ∈ interior s ↔ x ∈ ball (0 : E) 1 := by
    intro x
    rw [← hi]
    constructor
    · intro hx
      exact ⟨h.symm x, hx, h.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  have hd' : ∀ x, h.symm x ∈ s ↔ x ∈ closedBall (0 : E) 1 := by
    intro x
    rw [← hd]
    constructor
    · intro hx
      exact ⟨h.symm x, hx, h.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  let χ : PartialEquiv E E :=
    { toFun := fun x ↦ h.symm (ρ x)
      invFun := h
      source := ball 0 1
      target := interior s
      map_source' := by
        intro x hx
        rw [hρfix x (ball_subset_closedBall hx)]
        exact (hi' x).mpr hx
      map_target' := by
        intro x hx
        rw [← hi]
        exact mem_image_of_mem h hx
      left_inv' := by
        intro x hx
        simpa using hρfix x (ball_subset_closedBall hx)
      right_inv' := by
        intro x hx
        have hx' : h x ∈ closedBall (0 : E) 1 := by
          rw [← hd]
          exact mem_image_of_mem h (interior_subset hx)
        rw [hρfix (h x) hx', h.symm_apply_apply] }
  have heq : EqOn (χ : E → E) h.symm (closedBall 0 1) := by
    intro x hx
    change h.symm (ρ x) = h.symm x
    rw [hρfix x hx]
  refine ⟨χ, rfl, rfl, h.symm.continuous.comp hρcont, h.continuous,
    (fun x ↦ (hd' _).mpr (hρmem x)), ?_, ?_, ?_⟩
  · rw [heq.image_eq, ← hd, ← image_comp]
    simp
  · rw [(heq.mono ball_subset_closedBall).image_eq, ← hi, ← image_comp]
    simp
  · rw [(heq.mono sphere_subset_closedBall).image_eq, ← hf, ← image_comp]
    simp

end HolomorphicAnosov
