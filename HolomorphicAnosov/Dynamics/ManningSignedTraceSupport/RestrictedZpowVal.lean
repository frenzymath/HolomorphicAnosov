import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.RestrictedIterateVal

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter

open Set Filter _root_.Topology
open scoped BigOperators ENNReal Classical
noncomputable section

/-- Every integer power of the restriction of `f` to `Λ` agrees with the ambient value of the corresponding integer power of `f`. -/
theorem restricted_zpow_val {M : Type*} [TopologicalSpace M] (f : M ≃ₜ M) (Λ : Set M)
    (hΛ : ∀ x : M, x ∈ Λ ↔ f x ∈ Λ) (j : ℤ) (x : Λ) :
    (((f.subtype hΛ) ^ j) x).val = (f ^ j) x.val := by
  have hinv : ∀ (n : ℕ) (x : Λ), (((f.subtype hΛ).symm ^ n) x).val = (f.symm ^ n) x.val := by
    intro n x
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [pow_succ', Homeomorph.mul_apply]
        exact congrArg f.symm ih
  cases j with
  | ofNat n => exact restricted_iterate_val f Λ hΛ x n
  | negSucc n =>
      simp only [zpow_negSucc]
      have h := hinv (n+1) x
      change ↑(((f.subtype hΛ)⁻¹ ^ (n+1)) x) = (f⁻¹ ^ (n+1)) ↑x at h
      simpa only [inv_pow] using h


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter
