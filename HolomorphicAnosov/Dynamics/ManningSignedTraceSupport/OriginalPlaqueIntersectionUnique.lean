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

/-- Two points in the same original stable and unstable plaques are equal when the plaque radius is at most half the expansivity constant. -/
theorem original_plaque_intersection_unique {X : Type*} [MetricSpace X]
 (F : X ≃ₜ X) {e b : ℝ} (hb : 2*b ≤ e)
 (hexp : ∀ x y : X, (∀ j : ℤ, dist ((F^j) x) ((F^j) y) ≤ e) → x=y)
 {x y z w : X}
 (hz : z ∈ localStable F dist b x ∧ z ∈ localUnstable F dist b y)
 (hw : w ∈ localStable F dist b x ∧ w ∈ localUnstable F dist b y) : w=z := by
 apply hexp
 intro j
 by_cases hj : 0 ≤ j
 · have hj' : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj
   have hz' := hz.1 j.toNat
   have hw' := hw.1 j.toNat
   have hdist := (dist_triangle ((F^j) w) ((F^j) x) ((F^j) z))
   have h1 : dist ((F^j) w) ((F^j) x) ≤ b := by simpa only [← zpow_natCast, hj'] using hw'
   have h2 : dist ((F^j) x) ((F^j) z) ≤ b := by simpa only [dist_comm, ← zpow_natCast, hj'] using hz'
   linarith
 · have hj' : (-((-j).toNat : ℤ)) = j := by rw [Int.toNat_of_nonneg (by omega)]; omega
   have hz' := hz.2 (-j).toNat
   have hw' := hw.2 (-j).toNat
   have hdist := dist_triangle ((F^j) w) ((F^j) y) ((F^j) z)
   have h1 : dist ((F^j) w) ((F^j) y) ≤ b := by simpa only [hj'] using hw'
   have h2 : dist ((F^j) y) ((F^j) z) ≤ b := by simpa only [dist_comm, hj'] using hz'
   linarith


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter
