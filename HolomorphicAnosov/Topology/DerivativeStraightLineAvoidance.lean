import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.Linarith

/-!
# Avoidance of zero during local linearization

This is the analytic local-linearization step in the degree computation of Hatcher,
*Algebraic Topology*, §2.2, Proposition 2.30, p.136. The estimate is an agent-written
expansion of the derivative comparison used by `topo.disk_degree_local_homeomorphism_count`.
-/

open Filter Metric
open scoped Topology _root_.Topology

namespace HolomorphicAnosov.Topology

/-- Near a point with invertible derivative, the straight segment from the derivative
to the translated function avoids zero away from the base point, uniformly in time.

Proof: the derivative remainder is little-o of the displacement. The inverse continuous
linear map bounds the displacement by its linear image, so the remainder is eventually
at most half the norm of the linear image. Multiplication by a time in `[0,1]` cannot
increase this norm, and thus cannot cancel the nonzero linear image. No continuity away
from the base point, finite dimension, or positive determinant is needed for this estimate.
Source: analytic expansion of the local-degree comparison in the parent node
`topo.disk_degree_local_homeomorphism_count` (Hatcher §2.2, p.136). -/
theorem exists_radius_derivative_straightLine_ne_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {a : E} (A : E ≃L[ℝ] F)
    (hf : HasFDerivAt f (A : E →L[ℝ] F) a) :
    ∃ δ > 0, ∀ v : E, ‖v‖ < δ → v ≠ 0 → ∀ t : unitInterval,
      A v + (t : ℝ) • (f (a + v) - f a - A v) ≠ 0 := by
  have hsmall := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hf).trans_isBigO
    (A.isBigO_comp_rev (fun v : E ↦ v) (𝓝 0))
  obtain ⟨δ, hδ, hbound⟩ := Metric.eventually_nhds_iff.mp (hsmall.def (by norm_num : (0 : ℝ) < 1 / 2))
  refine ⟨δ, hδ, ?_⟩
  intro v hv hv0 t hzero
  have hrem := hbound (by simpa [dist_zero_right] using hv)
  change ‖f (a + v) - f a - A v‖ ≤ 1 / 2 * ‖A v‖ at hrem
  have hpos : 0 < ‖A v‖ := norm_pos_iff.mpr (by simpa using hv0)
  have ht : ‖(t : ℝ)‖ ≤ 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg t.property.1] using t.property.2
  have hnorm : ‖A v‖ = ‖(t : ℝ) • (f (a + v) - f a - A v)‖ := by
    exact (congrArg norm (eq_neg_of_add_eq_zero_left hzero)).trans (norm_neg _)
  have hle : ‖(t : ℝ) • (f (a + v) - f a - A v)‖ ≤
      ‖f (a + v) - f a - A v‖ := by
    rw [norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) ht
  linarith


end HolomorphicAnosov.Topology
