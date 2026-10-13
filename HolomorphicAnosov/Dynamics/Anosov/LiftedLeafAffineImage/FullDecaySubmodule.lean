import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

open scoped Topology _root_.Topology
open Filter Set

namespace HolomorphicAnosov

noncomputable section

/-- The actual full forward-decay set, closed under the real vector operations by limit laws. -/
def fullDecaySubmodule
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V ≃L[ℝ] V) : Submodule ℝ V where
  carrier := {v | Tendsto (fun n : ℕ ↦ (A : V → V)^[n] v) atTop (𝓝 0)}
  zero_mem' := by
    have hz : ∀ n : ℕ, (A : V → V)^[n] 0 = 0 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => simp [Function.iterate_succ_apply', ih]
    simpa only [Set.mem_ofPred_eq, hz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : V)) atTop (𝓝 0))
  add_mem' := by
    intro v w hv hw
    have ha : ∀ n : ℕ, (A : V → V)^[n] (v + w) =
        (A : V → V)^[n] v + (A : V → V)^[n] w := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => simp [Function.iterate_succ_apply', ih]
    simpa only [Set.mem_ofPred_eq, ha, add_zero] using hv.add hw
  smul_mem' := by
    intro c v hv
    have hs : ∀ n : ℕ, (A : V → V)^[n] (c • v) = c • (A : V → V)^[n] v := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => simp [Function.iterate_succ_apply', ih]
    simpa only [Set.mem_ofPred_eq, hs, smul_zero] using hv.const_smul c


end
end HolomorphicAnosov
