import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.StablePlaqueUniformTail

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter

open Set Filter _root_.Topology
open scoped BigOperators ENNReal Classical
noncomputable section

/-- Agent-expanded strict-buffer step. Uniform tail control handles indices at least N. Compact uniform continuity of the finite tuple of the first N iterates controls all preceding indices from a sufficiently small initial distance. Thus a closed forward c-plaque pair starting sufficiently close stays strictly r-close for every nonnegative time. The case N=0 is included by the empty finite product. -/
theorem stable_plaque_small_start_all_small {X : Type*} [MetricSpace X] [CompactSpace X]
    (F : X ≃ₜ X) {c : ℝ}
    (hc : ∀ x y : X, (∀ j : ℤ, dist ((F ^ j) x) ((F ^ j) y) ≤ c) → x = y)
    {r : ℝ} (hr : 0 < r) :
    ∃ a > 0, ∀ x y : X, dist x y < a →
      (∀ k : ℕ, dist ((F ^ (k : ℤ)) x) ((F ^ (k : ℤ)) y) ≤ c) →
      ∀ k : ℕ, dist ((F ^ (k : ℤ)) x) ((F ^ (k : ℤ)) y) < r := by
  obtain ⟨N, hN⟩ := stable_plaque_uniform_tail F hc hr
  let G : X → Fin N → X := fun x k ↦ (F ^ (k.val : ℤ)) x
  have hG : Continuous G := continuous_pi fun k ↦ (F ^ (k.val : ℤ)).continuous
  have huc : UniformContinuous G := CompactSpace.uniformContinuous_of_continuous hG
  obtain ⟨a, ha, hmod⟩ := Metric.uniformContinuous_iff.mp huc r hr
  refine ⟨a, ha, ?_⟩
  intro x y hxy hpl k
  by_cases hk : N ≤ k
  · exact hN x y hpl k hk
  · have hdist : dist (G x) (G y) < r := hmod hxy
    exact (dist_pi_lt_iff hr).mp hdist ⟨k, by omega⟩


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter
