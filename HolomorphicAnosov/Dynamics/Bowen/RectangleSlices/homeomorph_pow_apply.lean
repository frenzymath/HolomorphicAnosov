import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Constructions

namespace HolomorphicAnosov.Bowen.RectangleSlicesPreparation

open Set

theorem homeomorph_pow_apply {X : Type*} [TopologicalSpace X]
    (f : Homeomorph X X) (n : ℕ) (x : X) : (f ^ n) x = (f : X → X)^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Homeomorph.mul_apply, Function.iterate_succ_apply', ih]

end HolomorphicAnosov.Bowen.RectangleSlicesPreparation
