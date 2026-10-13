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

/-- A splice that follows a past code over y and future code over x is the actual point y when y is in the original closed b-stable plaque of x. Negative indices have distance less than epsilon from y; nonnegative indices have distance at most epsilon+b by the triangle inequality. Original e-expansivity identifies the image. No future labels of y are assumed beforehand. -/
theorem stable_splice_image_eq {X : Type*} [MetricSpace X]
 (F : X ≃ₜ X) {e b ε : ℝ} (hb : 0 ≤ b) (hsum : ε+b ≤ e)
 (hexp : ∀ x y : X, (∀ j : ℤ, dist ((F^j) x) ((F^j) y) ≤ e) → x=y)
 {x y z : X} (hstable : y ∈ localStable F dist b x)
 (hf : ∀ j : ℤ, 0 ≤ j → dist ((F^j) z) ((F^j) x)<ε)
 (hp : ∀ j : ℤ, j ≤ 0 → dist ((F^j) z) ((F^j) y)<ε) : z=y := by
 apply hexp
 intro j
 by_cases hj : 0 ≤ j
 · have hj' : (j.toNat : ℤ)=j := Int.toNat_of_nonneg hj
   have hy : dist ((F^j) x) ((F^j) y) ≤ b := by
    simpa only [← zpow_natCast,hj',dist_comm] using hstable j.toNat
   exact (dist_triangle _ _ _).trans ((add_le_add (hf j hj).le hy).trans hsum)
 · exact (hp j (by omega)).le.trans (by linarith)


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter
