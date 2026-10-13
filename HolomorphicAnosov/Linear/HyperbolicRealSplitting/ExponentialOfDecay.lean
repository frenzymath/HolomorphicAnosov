import HolomorphicAnosov.Linear.HyperbolicRealSplitting.ExponentialOfContractingPower
import HolomorphicAnosov.Linear.HyperbolicDecayComplement
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.SpecificLimits.Normed
import HolomorphicAnosov.Linear.HyperbolicRealSplitting.TendstoCLMZeroOfPointwise
import HolomorphicAnosov.Linear.HyperbolicRealSplitting.PowApplyNormLe

namespace HolomorphicAnosov

open Filter Topology _root_.Topology

theorem exponential_of_decay
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : V →L[ℝ] V) (hT : ∀ v, Tendsto (fun n ↦ (T ^ n) v) atTop (𝓝 0)) :
    ∃ C r : ℝ, 1 ≤ C ∧ 0 < r ∧ r < 1 ∧
      ∀ n v, ‖(T ^ n) v‖ ≤ C * r ^ n * ‖v‖ := by
  have hop := tendsto_clm_zero_of_pointwise (fun n ↦ T ^ n) hT
  have hnorm : Tendsto (fun n ↦ ‖T ^ n‖) atTop (𝓝 0) := by
    simpa using hop.norm
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hnorm.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)))
  let k := N + 1
  have hk : 0 < k := by omega
  exact exponential_of_contracting_power T k hk (hN k (by omega))

end HolomorphicAnosov
