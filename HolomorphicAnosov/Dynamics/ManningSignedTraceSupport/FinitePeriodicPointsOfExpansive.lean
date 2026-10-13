import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicZpowRemainder
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Homeomorph.Lemmas


namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set _root_.Topology
open scoped Classical
noncomputable section

/-- The fixed points of a positive iterate of an expansive homeomorphism of a compact
metric space form a finite set. This supplies Manning's finite periodic count directly:
continuity of the finite orbit segment isolates each periodic point, period reduction gives
all integer orbit bounds, and a compact discrete subset is finite. -/
theorem finite_periodicPoints_of_expansive {X : Type*} [MetricSpace X] [CompactSpace X]
    (F : X ≃ₜ X) {e : ℝ} (he : 0 < e)
    (hexp : ∀ x y : X,
      (∀ j : ℤ, dist ((F.toEquiv ^ j) x) ((F.toEquiv ^ j) y) ≤ e) → x = y)
    {m : ℕ} (hm : 0 < m) : Set.Finite {x : X | ((F : X → X)^[m]) x = x} := by
  let S : Set X := {x | ((F : X → X)^[m]) x = x}
  have hcompact : IsCompact S :=
    (isClosed_eq (F.continuous.iterate m) continuous_id).isCompact
  apply hcompact.finite
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro x hx
  let G : X → Fin m → X := fun y t ↦ ((F : X → X)^[t.val]) y
  have hG : Continuous G := continuous_pi fun t ↦ F.continuous.iterate t.val
  refine ⟨G ⁻¹' Metric.ball (G x) e, Metric.isOpen_ball.preimage hG, ?_⟩
  ext y
  constructor
  · rintro ⟨hnear, hy⟩
    apply Set.mem_singleton_iff.mpr
    apply hexp y x
    intro j
    rw [periodic_zpow_remainder F.toEquiv hm hy,
      periodic_zpow_remainder F.toEquiv hm hx]
    let t : Fin m := ⟨(j % (m : ℤ)).toNat, by
      have hrem := Int.emod_lt_of_pos j (show (0 : ℤ) < m by omega)
      have hnonneg := Int.emod_nonneg j (show (m : ℤ) ≠ 0 by omega)
      omega⟩
    exact ((dist_pi_lt_iff he).mp hnear t).le
  · intro hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    exact ⟨by simpa using he, hx⟩


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
