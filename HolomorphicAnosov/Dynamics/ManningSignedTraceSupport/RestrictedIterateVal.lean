import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter

open Set Filter _root_.Topology
open scoped BigOperators ENNReal Classical
noncomputable section

/-- Positive powers of the restriction of `f` to `Λ` agree with the ambient values of the corresponding powers of `f`. -/
theorem restricted_iterate_val {M : Type*} [TopologicalSpace M] (f : M ≃ₜ M) (Λ : Set M)
    (hΛ : ∀ x : M, x ∈ Λ ↔ f x ∈ Λ) (x : Λ) (n : ℕ) :
    (((f.subtype hΛ) ^ n) x).val = (f ^ n) x.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [pow_succ', Homeomorph.mul_apply]
      exact congrArg f ih


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter
