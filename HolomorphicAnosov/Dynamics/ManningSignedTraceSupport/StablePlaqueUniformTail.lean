import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.ExpansiveFiniteWindow

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter

open Set Filter _root_.Topology
open scoped BigOperators ENNReal Classical
noncomputable section

/-- Agent-expanded local-plaque comparison. Translate the finite expansive window forward by N, where N dominates the negatives of all window indices. Every resulting index is nonnegative, so the closed forward c-orbit condition applies there. The finite-window test makes every tail distance uniformly less than r; no exponential rate or transverse regularity is assumed. -/
theorem stable_plaque_uniform_tail {X : Type*} [MetricSpace X] [CompactSpace X]
    (F : X ≃ₜ X) {c : ℝ}
    (hc : ∀ x y : X, (∀ j : ℤ, dist ((F ^ j) x) ((F ^ j) y) ≤ c) → x = y)
    {r : ℝ} (hr : 0 < r) :
    ∃ N : ℕ, ∀ x y : X,
      (∀ k : ℕ, dist ((F ^ (k : ℤ)) x) ((F ^ (k : ℤ)) y) ≤ c) →
      ∀ n : ℕ, N ≤ n → dist ((F ^ (n : ℤ)) x) ((F ^ (n : ℤ)) y) < r := by
  classical
  obtain ⟨J, hJ⟩ := expansive_finite_window F hc hr
  let N := J.sup fun j ↦ (-j).toNat
  refine ⟨N, ?_⟩
  intro x y hxy n hn
  apply hJ
  intro j hj
  have hjN : (-j).toNat ≤ N := Finset.le_sup (f := fun j ↦ (-j).toNat) hj
  have hneg : -j ≤ (N : ℤ) :=
    (Int.self_le_toNat (-j)).trans (by exact_mod_cast hjN)
  have hnonneg : 0 ≤ j + (n : ℤ) := by omega
  have hindex : (((j + (n : ℤ)).toNat : ℕ) : ℤ) = j + (n : ℤ) :=
    Int.toNat_of_nonneg hnonneg
  simpa only [← Homeomorph.mul_apply, ← zpow_add, hindex] using
    hxy (j + (n : ℤ)).toNat


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter
