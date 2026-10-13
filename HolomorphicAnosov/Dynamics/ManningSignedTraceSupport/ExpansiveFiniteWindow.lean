import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter

open Set Filter _root_.Topology
open scoped BigOperators ENNReal Classical
noncomputable section

/-- Agent-expanded compactness step for the original Manning application. On the compact closed set of pairs separated by at least r, expansivity supplies an integer iterate whose distance exceeds c. These open witnesses have a finite subcover; requiring the c bound at its finitely many indices forces distance below r. Empty spaces and empty separated-pair sets need no exception. -/
theorem expansive_finite_window {X : Type*} [MetricSpace X] [CompactSpace X]
    (F : X ≃ₜ X) {c : ℝ}
    (hc : ∀ x y : X, (∀ j : ℤ, dist ((F ^ j) x) ((F ^ j) y) ≤ c) → x = y)
    {r : ℝ} (hr : 0 < r) :
    ∃ J : Finset ℤ, ∀ x y : X,
      (∀ j ∈ J, dist ((F ^ j) x) ((F ^ j) y) ≤ c) → dist x y < r := by
  classical
  let K : Set (X × X) := {p | r ≤ dist p.1 p.2}
  have hK : IsCompact K := (isClosed_le continuous_const
    (continuous_fst.dist continuous_snd)).isCompact
  let U : ℤ → Set (X × X) := fun j ↦ {p | c < dist ((F ^ j) p.1) ((F ^ j) p.2)}
  have hU : ∀ j, IsOpen (U j) := by
    intro j
    exact isOpen_lt continuous_const
      (((F ^ j).continuous.comp continuous_fst).dist
        ((F ^ j).continuous.comp continuous_snd))
  have hcover : K ⊆ ⋃ j, U j := by
    intro p hp
    by_contra h
    have hall : ∀ j : ℤ, dist ((F ^ j) p.1) ((F ^ j) p.2) ≤ c := by
      intro j
      exact le_of_not_gt (fun hj ↦ h (mem_iUnion.mpr ⟨j, hj⟩))
    have heq := hc p.1 p.2 hall
    have hz : dist p.1 p.2 = 0 := dist_eq_zero.mpr heq
    exact (not_le_of_gt hr) (hz ▸ hp)
  obtain ⟨J, hJ⟩ := hK.elim_finite_subcover U hU hcover
  refine ⟨J, ?_⟩
  intro x y hxy
  by_contra h
  have hp : (x, y) ∈ K := le_of_not_gt h
  obtain ⟨j, hj, hdist⟩ := mem_iUnion₂.mp (hJ hp)
  exact (not_lt_of_ge (hxy j hj)) hdist


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter
