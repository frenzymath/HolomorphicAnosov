import HolomorphicAnosov.Linear.HyperbolicDecayComplement
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.SpecificLimits.Normed

namespace HolomorphicAnosov

open Filter Topology _root_.Topology

theorem linear_pow_commutes
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V ≃ₗ[ℝ] V) (P : V →L[ℝ] V) (hP : ∀ v, P (A v) = A (P v)) :
    ∀ n : ℕ, ∀ v, P ((A ^ n) v) = (A ^ n) (P v) := by
  intro n
  induction n with
  | zero => intro v; rfl
  | succ n ih =>
    intro v
    rw [pow_succ', LinearEquiv.mul_apply, hP, ih, LinearEquiv.mul_apply]

end HolomorphicAnosov
