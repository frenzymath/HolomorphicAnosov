import HolomorphicAnosov.Linear.HyperbolicDecayComplement
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.SpecificLimits.Normed

namespace HolomorphicAnosov

open Filter Topology _root_.Topology

theorem pow_apply_norm_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : V →L[ℝ] V) (n : ℕ) (v : V) :
    ‖(T ^ n) v‖ ≤ ‖T‖ ^ n * ‖v‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      ‖(T ^ (n + 1)) v‖ = ‖T ((T ^ n) v)‖ := by rw [pow_succ']; rfl
      _ ≤ ‖T‖ * ‖(T ^ n) v‖ := T.le_opNorm _
      _ ≤ ‖T‖ * (‖T‖ ^ n * ‖v‖) := mul_le_mul_of_nonneg_left ih (norm_nonneg _)
      _ = ‖T‖ ^ (n + 1) * ‖v‖ := by rw [pow_succ]; ring

end HolomorphicAnosov
