import HolomorphicAnosov.Linear.HyperbolicDecayComplement
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.SpecificLimits.Normed

namespace HolomorphicAnosov

open Filter Topology _root_.Topology

theorem inverse_pow_cancel
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V ≃ₗ[ℝ] V) (n : ℕ) (v : V) : (A ^ n) ((A.symm ^ n) v) = v := by
  change (A ^ n * A.symm ^ n) v = v
  change (A ^ n * (A⁻¹) ^ n) v = v
  rw [inv_pow, mul_inv_cancel]; rfl

end HolomorphicAnosov
