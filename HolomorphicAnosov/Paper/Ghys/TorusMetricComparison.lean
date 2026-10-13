import HolomorphicAnosov.Geometry.Biholomorph
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.LatticeLinearEquiv
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Quotient
import Mathlib.Algebra.Group.Units.Equiv
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Charts
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.LinearMap
import HolomorphicAnosov.Paper.Zhang.Anosov
import Mathlib.LinearAlgebra.Eigenspace.Basic
import HolomorphicAnosov.Paper.Zhang.FixedBlockUniformAnosovEstimates
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Complex.Basic
import HolomorphicAnosov.Paper.Ghys.TorusCompact
import HolomorphicAnosov.Paper.Ghys.TorusMetricNorm
import HolomorphicAnosov.Paper.Ghys.TorusMetricNormContinuous
import HolomorphicAnosov.Paper.Ghys.TorusMetricNormSmul

namespace HolomorphicAnosov

open scoped ContDiff Topology _root_.Topology Manifold Bundle
open IsManifold
attribute [local instance] complexTorus_isManifold complex_isManifold_real
set_option backward.isDefEq.respectTransparency false

theorem torus_metric_comparison {d : ℕ} (L : FullComplexLattice d)
    (g : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : ComplexTorus L ↦ TangentSpace (realModel d) x)) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ x v,
      m * ‖v‖ ≤ torusMetricNorm L g x v ∧ torusMetricNorm L g x v ≤ M * ‖v‖ := by
  let := torus_compact L
  let S : Set (ComplexTorus L × ComplexModel d) := Set.univ ×ˢ Metric.sphere 0 1
  have hS : IsCompact S := isCompact_univ.prod (isCompact_sphere 0 1)
  have hN := torus_metric_norm_continuous L g
  obtain ⟨m, hm, hmin⟩ := hS.exists_forall_le' hN.continuousOn (a := 0) (by
    intro p hp
    apply Real.sqrt_pos.2
    apply g.pos
    have hn : ‖p.2‖ = 1 := by simpa using hp.2
    intro hz
    simp [hz] at hn)
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hN.continuousOn
  let M := max 1 B
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨m, M, hm, hM, fun x v ↦ ?_⟩
  by_cases hv : v = 0
  · simp [hv, torusMetricNorm]
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w : ComplexModel d := ‖v‖⁻¹ • v
  have hwn : ‖w‖ = 1 := by simp [w, norm_smul, hvn.ne']
  have hw : (x, w) ∈ S := ⟨Set.mem_univ _, by simpa using hwn⟩
  have hl : m ≤ torusMetricNorm L g x w := hmin _ hw
  have hu : torusMetricNorm L g x w ≤ M :=
    (le_abs_self _).trans ((hB _ hw).trans (le_max_right _ _))
  have heq : torusMetricNorm L g x w = ‖v‖⁻¹ * torusMetricNorm L g x v := by
    simpa [w, abs_of_pos (inv_pos.mpr hvn)] using torus_metric_norm_smul L g x ‖v‖⁻¹ v
  rw [heq] at hl hu
  constructor
  · have hh := mul_le_mul_of_nonneg_right hl hvn.le
    simpa only [mul_assoc, mul_left_comm, inv_mul_cancel₀ hvn.ne', mul_one] using hh
  · have hh := mul_le_mul_of_nonneg_right hu hvn.le
    simpa only [mul_assoc, mul_left_comm, inv_mul_cancel₀ hvn.ne', mul_one] using hh

end HolomorphicAnosov
