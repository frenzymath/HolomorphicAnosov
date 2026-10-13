import HolomorphicAnosov.Linear.HyperbolicDecayComplement
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.SpecificLimits.Normed
import HolomorphicAnosov.Linear.HyperbolicRealSplitting.ExponentialOfContractingPower
import HolomorphicAnosov.Linear.HyperbolicRealSplitting.TendstoCLMZeroOfPointwise

namespace HolomorphicAnosov

open Filter Topology _root_.Topology

theorem restricted_exponential
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (A : V ≃L[ℝ] V) (S : Submodule ℝ V)
    (hS : ∀ v ∈ S, A v ∈ S)
    (hdec : ∀ v ∈ S, Tendsto (fun n : ℕ ↦ (A ^ n) v) atTop (𝓝 0)) :
    ∃ C r : ℝ, 1 ≤ C ∧ 0 < r ∧ r < 1 ∧
      ∀ n v, v ∈ S → ‖(A ^ n) v‖ ≤ C * r ^ n * ‖v‖ := by
  let T : S →L[ℝ] S := (A.toContinuousLinearMap.toLinearMap.restrict hS).toContinuousLinearMap
  have heq : ∀ n (v : S), ((T ^ n) v : V) = (A ^ n) v := by
    intro n
    induction n with
    | zero => intro v; rfl
    | succ n ih =>
      intro v
      rw [pow_succ', pow_succ']
      change A ((T ^ n) v : V) = A ((A ^ n) v)
      rw [ih]
  have hT : ∀ v : S, Tendsto (fun n : ℕ ↦ (T ^ n) v) atTop (𝓝 0) := by
    intro v
    apply Topology.IsEmbedding.subtypeVal.tendsto_nhds_iff.mpr
    change Tendsto (fun n : ℕ ↦ ((T ^ n) v : V)) atTop (𝓝 0)
    simpa only [heq] using hdec v v.property
  have hop := tendsto_clm_zero_of_pointwise (fun n ↦ T ^ n) hT
  have hnorm : Tendsto (fun n ↦ ‖T ^ n‖) atTop (𝓝 0) := by
    simpa using hop.norm
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hnorm.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)))
  obtain ⟨C, r, hC, hr, hr1, hbound⟩ :=
    exponential_of_contracting_power T (N + 1) (by omega) (hN (N + 1) (by omega))
  exact ⟨C, r, hC, hr, hr1, fun n v hv ↦ by
    simpa [← heq n ⟨v, hv⟩] using hbound n ⟨v, hv⟩⟩

end HolomorphicAnosov
