import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.CompatibleMetricModulus
import Mathlib.Algebra.Group.End

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter

open Set Filter _root_.Topology
open scoped BigOperators ENNReal Classical
noncomputable section

/-- Apply the reverse identity modulus at an expansive bound and halve its
input radius. Integer orbit distances at most the half radius therefore meet
the original expansive test. No dynamical or connectedness assumption is added. -/
theorem compatible_metric_expansivity {X : Type*} [old : MetricSpace X] [CompactSpace X]
    (new : MetricSpace X)
    (ht : new.toUniformSpace.toTopologicalSpace = old.toUniformSpace.toTopologicalSpace)
    (F : Equiv.Perm X) {e : ℝ} (he : 0 < e)
    (hexp : ∀ x y : X, (∀ j : ℤ, new.dist ((F ^ j) x) ((F ^ j) y) ≤ e) → x = y) :
    ∃ d > 0, ∀ x y : X,
      (∀ j : ℤ, old.dist ((F ^ j) x) ((F ^ j) y) ≤ d) → x = y := by
  obtain ⟨d, hd, hmod⟩ := @compatible_metric_modulus X new
    (ht.symm ▸ (inferInstance : @CompactSpace X old.toUniformSpace.toTopologicalSpace))
    old ht.symm e he
  refine ⟨d / 2, half_pos hd, ?_⟩
  intro x y h
  apply hexp x y
  intro j
  exact (hmod _ _ ((h j).trans_lt (half_lt_self hd))).le


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter
