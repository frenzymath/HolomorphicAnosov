import HolomorphicAnosov.Linear.HyperbolicDecayComplement
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.SpecificLimits.Normed

namespace HolomorphicAnosov

open Filter Topology _root_.Topology

theorem decay_invariant
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A B : V ≃L[ℝ] V) (hc : Commute A B) (v : V)
    (hv : Tendsto (fun n : ℕ ↦ (A ^ n) v) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ (A ^ n) (B v)) atTop (𝓝 0) := by
  have h := B.continuous.tendsto 0 |>.comp hv
  have heq : ∀ n : ℕ, B ((A ^ n) v) = (A ^ n) (B v) := fun n ↦
    congrArg (fun C : V ≃L[ℝ] V ↦ C v) (hc.pow_left n).eq.symm
  simpa only [Function.comp_def, map_zero, heq] using h

end HolomorphicAnosov
