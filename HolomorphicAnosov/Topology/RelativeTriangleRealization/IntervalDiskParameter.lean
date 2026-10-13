import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Topology.UnitInterval

noncomputable section
open Set Topology _root_.Topology Metric
namespace HolomorphicAnosov.RelativeTriangleRealization
universe u

/-- Specialization of Mathlib's simplex-to-interval and affine interval
homeomorphisms to the native one-dimensional CW disk. Source:
`Convexity.StdSimplex.homeomorphI`, `iccHomeoI`, and the finite-product norm.
The affine map is 2*t₁-1. The sum of the two barycentric coordinates is one,
so its norm is strictly less than one exactly when both coordinates are
strictly positive. -/
theorem intervalDiskParameter :
    ∃ disk : Convexity.StdSimplex ℝ (Fin 2) ≃ₜ Metric.closedBall (0 : Fin 1 → ℝ) 1,
      ∀ t, (disk t).val ∈ Metric.ball (0 : Fin 1 → ℝ) 1 ↔
        ∀ j, 0 < t.weights j := by
  let e : Set.Icc (-1 : ℝ) 1 ≃ₜ Metric.closedBall (0 : Fin 1 → ℝ) 1 := {
    toFun := fun t ↦ ⟨fun _ ↦ t.val, by
      simpa only [Metric.mem_closedBall, dist_zero_right, pi_norm_const,
        Real.norm_eq_abs, abs_le, Set.mem_Icc] using t.property⟩
    invFun := fun x ↦ ⟨x.val 0, by
      have hnorm : ‖x.val‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
      have h0 : |x.val 0| ≤ 1 := (norm_le_pi_norm x.val 0).trans hnorm
      exact abs_le.mp h0⟩
    left_inv := fun t ↦ rfl
    right_inv := fun x ↦ by
      apply Subtype.ext
      funext i
      exact congrArg x.val (Subsingleton.elim _ _)
    continuous_toFun := by fun_prop
    continuous_invFun := by
      apply Continuous.subtype_mk
      exact (continuous_apply 0).comp continuous_subtype_val }
  let disk := Convexity.StdSimplex.homeomorphI.trans
    ((iccHomeoI (-1 : ℝ) 1 (by norm_num)).symm.trans e)
  refine ⟨disk, ?_⟩
  intro t
  have htotal : t.weights 0 + t.weights 1 = 1 := by
    exact t.total_fin_two
  change (fun _ : Fin 1 ↦ (1 - (-1 : ℝ)) * t.weights 1 + (-1)) ∈
    Metric.ball (0 : Fin 1 → ℝ) 1 ↔ ∀ j, 0 < t.weights j
  simp only [Metric.mem_ball, dist_zero_right, pi_norm_const, Real.norm_eq_abs, abs_lt]
  constructor
  · intro h j
    fin_cases j <;> dsimp <;> linarith
  · intro h
    have h0 := h 0
    have h1 := h 1
    constructor <;> linarith

end HolomorphicAnosov.RelativeTriangleRealization
