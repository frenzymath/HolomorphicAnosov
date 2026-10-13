import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Moving the cone peak inside its characteristic disk

Fritsch–Piccinini, Cellular Structures in Topology, Lemma 2.3.7, p.67,
asserts that the cone homeomorphism can place its peak at the marked point.
The proof below expands that omitted choice in the native maximum norm,
using the global small-perturbation homeomorphism theorem from Mathlib.
-/

namespace HolomorphicAnosov

/-- A boundary-fixing homeomorphism of the closed max-norm unit disk carries
its origin to any prescribed interior point.

Source context: Fritsch–Piccinini Lemma 2.3.7, p.67. This explicit proof is an
agent-written expansion of its unspecified homeomorphism choice. Put
`f(v)=v+(1-‖v‖)a`. The perturbation has Lipschitz constant at most `‖a‖<1`,
so Mathlib's global inverse theorem makes f a homeomorphism. The norm triangle
inequality puts f(v) inside the closed disk whenever v is inside; the reverse
norm inequality shows f(v) is outside whenever v is outside. Thus f restricts
to a homeomorphism of the disk. Its formula fixes the boundary and sends 0 to a.
Zero-dimensional disks are included. -/
theorem cw_vertex_disk_homeomorph {n : ℕ} (a : Fin n → ℝ) (ha : ‖a‖ < 1) :
    ∃ H : Metric.closedBall (0 : Fin n → ℝ) 1 ≃ₜ
        Metric.closedBall (0 : Fin n → ℝ) 1,
      (∀ v, (H v).val = v.val + (1 - ‖v.val‖) • a) ∧
      (H ⟨0, by simp⟩).val = a ∧
      ∀ v, ‖v.val‖ = 1 → H v = v := by
  let move : (Fin n → ℝ) → (Fin n → ℝ) := fun v ↦ v + (1 - ‖v‖) • a
  have happrox : ApproximatesLinearOn move
      (ContinuousLinearEquiv.refl ℝ (Fin n → ℝ)).toContinuousLinearMap
      Set.univ ‖a‖₊ := by
    intro v _ w _
    have hdiff : move v - move w - (v - w) = (‖w‖ - ‖v‖) • a := by
      ext k
      simp only [move, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    change ‖move v - move w - (v - w)‖ ≤ ‖a‖ * ‖v - w‖
    rw [hdiff, norm_smul, Real.norm_eq_abs]
    calc
      |‖w‖ - ‖v‖| * ‖a‖ ≤ ‖w - v‖ * ‖a‖ :=
        mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le w v) (norm_nonneg a)
      _ = ‖a‖ * ‖v - w‖ := by rw [norm_sub_rev, mul_comm]
  have hsmall : Subsingleton (Fin n → ℝ) ∨
      ‖a‖₊ < ‖((ContinuousLinearEquiv.refl ℝ (Fin n → ℝ)).symm :
        (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖₊⁻¹ := by
    by_cases hs : Subsingleton (Fin n → ℝ)
    · exact Or.inl hs
    · let : Nontrivial (Fin n → ℝ) := not_subsingleton_iff_nontrivial.mp hs
      right
      have haNN : ‖a‖₊ < 1 := by exact_mod_cast ha
      simpa using haNN
  let moveHomeomorph : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) :=
    happrox.toHomeomorph move hsmall
  have hclosed (v : Fin n → ℝ) : ‖move v‖ ≤ 1 ↔ ‖v‖ ≤ 1 := by
    constructor
    · intro hv
      by_contra hv'
      have hpos : 1 < ‖v‖ := lt_of_not_ge hv'
      have hdiff : v - move v = (‖v‖ - 1) • a := by
        ext k
        simp only [move, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      have hnorm := norm_sub_norm_le v (move v)
      rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hpos)] at hnorm
      nlinarith
    · intro hv
      have hcoeff : 0 ≤ 1 - ‖v‖ := sub_nonneg.mpr hv
      calc
        ‖move v‖ ≤ ‖v‖ + ‖(1 - ‖v‖) • a‖ := norm_add_le _ _
        _ = ‖v‖ + (1 - ‖v‖) * ‖a‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoeff]
        _ ≤ ‖v‖ + (1 - ‖v‖) * 1 :=
          add_le_add_right (mul_le_mul_of_nonneg_left ha.le hcoeff) _
        _ = 1 := by ring
  let diskMove : Metric.closedBall (0 : Fin n → ℝ) 1 ≃ₜ
      Metric.closedBall (0 : Fin n → ℝ) 1 := moveHomeomorph.subtype (by
    intro v
    change v ∈ Metric.closedBall 0 1 ↔ move v ∈ Metric.closedBall 0 1
    simpa only [Metric.mem_closedBall, dist_zero_right] using (hclosed v).symm)
  refine ⟨diskMove, ?_, ?_, ?_⟩
  · intro v
    rfl
  · change move 0 = a
    simp [move]
  · intro v hv
    apply Subtype.ext
    change move v = v.val
    simp [move, hv]

end HolomorphicAnosov
