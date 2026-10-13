import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.Definitions
import Mathlib.Topology.ContinuousMap.Algebra

/-! # Confining a punctured homotopy to a Jordan closure

This is the radial-clamp step in the Jordan-region part of the
Lehto--Virtanen argument.  It is stated independently of the construction of
the punctured homotopy: a Schoenflies chart carries the region and its closure
to the open and closed unit disks, and radial clamping in that chart keeps the
homotopy in the closure while preserving its endpoints and its omitted point.
Source: Cairns, *An Elementary Proof of the Jordan-Schoenflies Theorem*
(1951), pp.860--867, together with the radial deformation used in the proof
of the Jordan-region confinement step.
-/

namespace HolomorphicAnosov

open Set
open scoped _root_.Topology

/-- Radially clamp an already punctured homotopy to the closure of a Jordan
region represented by a Schoenflies chart.  The chart hypotheses are explicit
so this proposition does not assume a hidden identification of a given open
connected set with a complementary component.

The proposition is reusable whenever a boundary parametrization supplies the
endpoint range in `closure Q`; the clamp fixes every point of that closed disk.
The interior point `a` cannot be hit by a clamped point outside the disk,
since radial clamping sends every exterior point to the unit circle. -/
theorem qc_confine_punctured_homotopy
    (Q : Set ℂ) (E : ℂ ≃ₜ ℂ)
    (hQ : E '' Q = Metric.ball (0 : ℂ) 1)
    (hclosureQ : E '' closure Q = Metric.closedBall (0 : ℂ) 1)
    (a : ℂ) (ha : a ∈ Q)
    (H : C(↑unitInterval × Circle, ℂ))
    (hstart : ∀ z : Circle, H (0, z) ∈ closure Q)
    (hend : ∀ z : Circle, H (1, z) ∈ closure Q)
    (havoid : ∀ (t : unitInterval) (z : Circle), H (t, z) ≠ a) :
    ∃ K : C(↑unitInterval × Circle, ℂ),
      (∀ z : Circle, K (0, z) = H (0, z)) ∧
      (∀ z : Circle, K (1, z) = H (1, z)) ∧
      (∀ (t : unitInterval) (z : Circle), K (t, z) ∈ closure Q) ∧
      (∀ (t : unitInterval) (z : Circle), K (t, z) ≠ a) := by
  let ρ : ℂ → ℂ := fun x ↦ (max (1 : ℝ) ‖x‖)⁻¹ • x
  have hmax : Continuous (fun x : ℂ ↦ max (1 : ℝ) ‖x‖) :=
    continuous_const.max continuous_norm
  have hmax_pos (x : ℂ) : 0 < max (1 : ℝ) ‖x‖ :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hρ : Continuous ρ := by
    exact (hmax.inv₀ (fun x ↦ ne_of_gt (hmax_pos x))).smul continuous_id
  have hρfix (x : ℂ) (hx : x ∈ Metric.closedBall (0 : ℂ) 1) : ρ x = x := by
    have hx' : ‖x‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
    change (max (1 : ℝ) ‖x‖)⁻¹ • x = x
    rw [show max (1 : ℝ) ‖x‖ = 1 by exact max_eq_left hx']
    simp
  have hρmem (x : ℂ) : ρ x ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    by_cases hx : ‖x‖ ≤ 1
    · change ‖(max (1 : ℝ) ‖x‖)⁻¹ • x‖ ≤ 1
      rw [max_eq_left hx]
      simpa using hx
    · have hx' : 1 < ‖x‖ := lt_of_not_ge hx
      have hxpos : 0 < ‖x‖ := lt_trans zero_lt_one hx'
      simp [ρ, max_eq_right hx'.le, hxpos.ne']
  have hρeq (x b : ℂ) (hb : b ∈ Metric.ball (0 : ℂ) 1)
      (heq : ρ x = b) : x = b := by
    have hb' : ‖b‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hb
    by_cases hx : ‖x‖ ≤ 1
    · simpa [ρ, max_eq_left hx] using heq
    · have hx' : 1 < ‖x‖ := lt_of_not_ge hx
      have hxnorm : ‖ρ x‖ = 1 := by
        have hxpos : 0 < ‖x‖ := lt_trans zero_lt_one hx'
        simp [ρ, max_eq_right hx'.le, hxpos.ne']
      have := congrArg norm heq
      rw [hxnorm] at this
      exact False.elim ((not_lt_of_ge (le_of_eq this)) hb')
  have hEa : E a ∈ Metric.ball (0 : ℂ) 1 := by
    rw [← hQ]
    exact ⟨a, ha, rfl⟩
  let Φ : ℂ → ℂ := fun x ↦ E.symm (ρ (E x))
  have hΦ : Continuous Φ := E.symm.continuous.comp (hρ.comp E.continuous)
  let K : C(↑unitInterval × Circle, ℂ) :=
    ⟨fun tz ↦ Φ (H tz), hΦ.comp H.continuous⟩
  have hΦfix (x : ℂ) (hx : x ∈ closure Q) : Φ x = x := by
    have hEx : E x ∈ Metric.closedBall (0 : ℂ) 1 := by
      rw [← hclosureQ]
      exact ⟨x, hx, rfl⟩
    dsimp [Φ]
    rw [hρfix _ hEx, E.symm_apply_apply]
  refine ⟨K, ?_, ?_, ?_, ?_⟩
  · intro z
    dsimp [K]
    rw [hΦfix _ (hstart z)]
  · intro z
    dsimp [K]
    rw [hΦfix _ (hend z)]
  · intro t z
    have hρdisk : ρ (E (H (t, z))) ∈ Metric.closedBall (0 : ℂ) 1 :=
      hρmem _
    have himage : ρ (E (H (t, z))) ∈ E '' closure Q := by
      rw [hclosureQ]
      exact hρdisk
    rcases himage with ⟨y, hy, hEy⟩
    have hval : E.symm (ρ (E (H (t, z)))) = y := by
      apply E.injective
      rw [E.apply_symm_apply]
      exact hEy.symm
    change E.symm (ρ (E (H (t, z)))) ∈ closure Q
    simpa [hval] using hy
  · intro t z hK
    have hρa : ρ (E (H (t, z))) = E a := by
      have hcong := congrArg E hK
      simpa [K, Φ] using hcong
    have hHE : E (H (t, z)) = E a := hρeq _ _ hEa hρa
    exact havoid t z (E.injective hHE)

end HolomorphicAnosov

