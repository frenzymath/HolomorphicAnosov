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

/-- The inverse counterpart: a splice following the past of x and future of y has image y when y is in the original closed b-unstable plaque of x. Nonnegative indices are directly epsilon-close to y, while negative ones are at most epsilon+b-close. Original expansivity supplies equality before any source membership of the inverse image is inferred. -/
theorem unstable_splice_image_eq {X : Type*} [MetricSpace X]
 (F : X ≃ₜ X) {e b ε : ℝ} (hb : 0 ≤ b) (hsum : ε+b ≤ e)
 (hexp : ∀ x y : X, (∀ j : ℤ, dist ((F^j) x) ((F^j) y) ≤ e) → x=y)
 {x y z : X} (hunstable : y ∈ localUnstable F dist b x)
 (hf : ∀ j : ℤ, 0 ≤ j → dist ((F^j) z) ((F^j) y)<ε)
 (hp : ∀ j : ℤ, j ≤ 0 → dist ((F^j) z) ((F^j) x)<ε) : z=y := by
 apply hexp
 intro j
 by_cases hj : 0 ≤ j
 · exact (hf j hj).le.trans (by linarith)
 · have hj' : -((-j).toNat : ℤ)=j := by
    rw [Int.toNat_of_nonneg (by omega)]; omega
   have hy : dist ((F^j) x) ((F^j) y) ≤ b := by
    simpa only [hj',dist_comm] using hunstable (-j).toNat
   exact (dist_triangle _ _ _).trans ((add_le_add (hp j (by omega)).le hy).trans hsum)


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter
