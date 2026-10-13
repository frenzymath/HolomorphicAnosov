import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith
import HolomorphicAnosov.Dynamics.Bowen.BowenBasicSetMarkovCoding

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter

open Set Filter _root_.Topology
open scoped BigOperators ENNReal Classical
noncomputable section
open BowenBasicSetCoding

/-- The rectangle cover is expansive: two points whose full integer orbits remain within the expansivity bound are equal. -/
theorem rectangle_cover_expansive {X : Type*} [MetricSpace X]
    (F : X ≃ₜ X) {γ : ℝ} (hγ : 0 < γ) {N : ℕ} (R : Fin N → Set X)
    (hR : ∀ i, BowenBasicSetCoding.IsRectangle F dist γ (R i))
    (hcover : ∀ x : X, ∃ i, x ∈ R i) :
    ∀ x y : X, (∀ j : ℤ, dist ((F ^ j) x) ((F ^ j) y) ≤ γ) → x = y := by
  intro x y hxy
  obtain ⟨i, hxi⟩ := hcover x
  obtain ⟨z, hz, hu⟩ := (hR i).2.2.2 x hxi x hxi
  have hself : x = z := (hu x).mp (by simp [BowenBasicSetCoding.localStable, BowenBasicSetCoding.localUnstable, hγ.le])
  have hy : y = z := (hu y).mp ⟨by
    intro k
    simpa only [dist_comm, zpow_natCast] using hxy (k : ℤ), by
    intro k
    simpa only [dist_comm] using hxy (-(k : ℤ))⟩
  exact hself.trans hy.symm


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter
