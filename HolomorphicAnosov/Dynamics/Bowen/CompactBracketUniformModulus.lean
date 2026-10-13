import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor

open Set

namespace HolomorphicAnosov.Bowen

/--
On a compact pair core, continuity of Bowen's bracket has a uniform modulus.
This is the compact-uniform-continuity step used when shrinking the initial
seed factors in Bowen's construction (Bowen 1970, pp. 728--732).
-/
theorem compact_bracket_uniform_modulus
    {X : Type*} [MetricSpace X]
    (bracket : X → X → X) (K : Set (X × X)) (hK : IsCompact K)
    (hcont : ContinuousOn (fun p : X × X ↦ bracket p.1 p.2) K)
    {η : ℝ} (hη : 0 < η) :
    ∃ ρ > 0, ∀ p ∈ K, ∀ q ∈ K,
      dist p q < ρ → dist (bracket p.1 p.2) (bracket q.1 q.2) < η := by
  exact Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hcont) η hη

end HolomorphicAnosov.Bowen
