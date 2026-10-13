import Mathlib.Topology.Path
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic.Ring

/-!
# Prescribed loops on original one-cell disks

Source: Hatcher, *Algebraic Topology*, Proposition 1B.9 pp.90–91, assigning
a representative loop to each edge outside the maximal tree. The original
Mathlib one-disk is the maximum-norm closed unit ball in `Fin 1 → ℝ`.
The coordinate adapter is an agent-written expansion of this edge assignment.
-/

namespace HolomorphicAnosov

universe v

/-- Every based loop defines a continuous map on the original maximum-norm
one-disk, constant at the basepoint on its boundary, whose pullback under the
chosen affine parameter `t ↦ 2t - 1` or `t ↦ 1 - 2t` is exactly the prescribed loop.

Source context: Hatcher, Proposition 1B.9 pp.90–91. Agent-written coordinate
expansion: for the forward orientation compose the continuous extension of the
loop with `(z(0)+1)/2`; for the reverse orientation use `(1-z(0))/2`.
At the correspondingly oriented coordinate this parameter is exactly `t`,
where the path extension equals the original loop. In dimension one the maximum norm is the absolute value
of the unique coordinate. Thus the sphere consists of coordinates `-1` and
`1`, which map to parameters `0` and `1`; both endpoints equal the loop's
basepoint. This requires no topology or separation assumptions on the target
beyond being a topological space. The boundary conclusion covers every pair
of characteristic boundary points, even if they are identified.
DAG: `topo.cw_one_cell_loop_disk_realization_g4`.
-/
theorem cw_one_cell_loop_disk_realization
    {Y : Type v} [TopologicalSpace Y] {y₀ : Y} (ell : Path y₀ y₀) (rev : Bool) :
    ∃ b : C(Metric.closedBall (0 : Fin 1 → ℝ) 1, Y),
      (∀ (t : unitInterval) (z : Metric.closedBall (0 : Fin 1 → ℝ) 1),
        z.val 0 = (if rev then 1 - 2 * (t : ℝ) else 2 * (t : ℝ) - 1) →
          b z = ell t) ∧
      (∀ z : Metric.closedBall (0 : Fin 1 → ℝ) 1,
        ‖z.val‖ = 1 → b z = y₀) := by
  cases rev
  · let b : C(Metric.closedBall (0 : Fin 1 → ℝ) 1, Y) :=
      ⟨fun z ↦ ell.extend ((z.val 0 + 1) / 2),
        ell.extend.continuous.comp
          (((continuous_apply 0).comp continuous_subtype_val).add continuous_const |>.div_const 2)⟩
    refine ⟨b, ?_, ?_⟩
    · intro t z hz
      change ell.extend ((z.val 0 + 1) / 2) = ell t
      simp only [Bool.false_eq_true, ↓reduceIte] at hz
      rw [hz, show (2 * (t : ℝ) - 1 + 1) / 2 = t by ring]
      exact ell.extend_extends' t
    · intro z hz
      have habs : |z.val 0| = 1 := by
        have hf : z.val = fun _ : Fin 1 ↦ z.val 0 :=
          funext fun j ↦ congrArg z.val (Subsingleton.elim j 0)
        rw [hf, pi_norm_const, Real.norm_eq_abs] at hz
        exact hz
      rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs with h | h
      · change ell.extend ((z.val 0 + 1) / 2) = y₀
        rw [h]
        norm_num
      · change ell.extend ((z.val 0 + 1) / 2) = y₀
        rw [h]
        norm_num
  · let b : C(Metric.closedBall (0 : Fin 1 → ℝ) 1, Y) :=
      ⟨fun z ↦ ell.extend ((1 - z.val 0) / 2),
        ell.extend.continuous.comp
          ((continuous_const.sub ((continuous_apply 0).comp continuous_subtype_val)).div_const 2)⟩
    refine ⟨b, ?_, ?_⟩
    · intro t z hz
      change ell.extend ((1 - z.val 0) / 2) = ell t
      simp only [↓reduceIte] at hz
      rw [hz, show (1 - (1 - 2 * (t : ℝ))) / 2 = t by ring]
      exact ell.extend_extends' t
    · intro z hz
      have habs : |z.val 0| = 1 := by
        have hf : z.val = fun _ : Fin 1 ↦ z.val 0 :=
          funext fun j ↦ congrArg z.val (Subsingleton.elim j 0)
        rw [hf, pi_norm_const, Real.norm_eq_abs] at hz
        exact hz
      rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs with h | h
      · change ell.extend ((1 - z.val 0) / 2) = y₀
        rw [h]
        norm_num
      · change ell.extend ((1 - z.val 0) / 2) = y₀
        rw [h]
        norm_num


end HolomorphicAnosov
