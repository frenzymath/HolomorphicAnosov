import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ProperRelativeMarkovPartitionG7
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicZpowRemainder
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicWord
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicPhysicalPoints
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.OriginalTransition

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- A positive periodic word has at most one physical point in its relation. (Manning, pp. 216–219) -/
theorem periodicPhysicalPoints_subsingleton {M : Type*} [MetricSpace M]
    {f : M ≃ₜ M} {Λ : Set M} (P : ProperRelativeMarkovPartition f Λ)
    (e : ℝ)
    (hexp : ∀ x y : Λ,
      (∀ j : ℤ, dist ((P.onSet.toEquiv ^ j) x) ((P.onSet.toEquiv ^ j) y) ≤ e) → x = y)
    (hsmall : ∀ i, Metric.diam (P.rectangles i) < e)
    {r m : ℕ} (c : Composition (r + 1)) (hm : 0 < m)
    (w : PeriodicWord P.rectangles (originalTransition P) c hm) :
    (periodicPhysicalPoints P.rectangles (originalTransition P) c P.onSet hm w).Subsingleton := by
  intro x hx y hy
  apply hexp x y
  intro j
  rw [periodic_zpow_remainder P.onSet.toEquiv hm hx.1,
    periodic_zpow_remainder P.onSet.toEquiv hm hy.1]
  let t : Fin m := ⟨(j % (m : ℤ)).toNat, by
    have hrem := Int.emod_lt_of_pos j (show (0 : ℤ) < m by omega)
    have hnonneg := Int.emod_nonneg j (show (m : ℤ) ≠ 0 by omega)
    omega⟩
  let k : Fin c.length := ⟨0, c.length_pos_of_pos (Nat.succ_pos r)⟩
  obtain ⟨i, hi⟩ := (w.val t).property.1 k
  have hxi := hx.2 t k i hi
  have hyi := hy.2 t k i hi
  have hbounded : Bornology.IsBounded (P.rectangles i) := by
    let : CompactSpace Λ := isCompact_iff_compactSpace.mp P.compact
    exact Metric.isBounded_of_compactSpace
  exact (Metric.dist_le_diam_of_mem hbounded hxi hyi).trans (hsmall i).le


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
