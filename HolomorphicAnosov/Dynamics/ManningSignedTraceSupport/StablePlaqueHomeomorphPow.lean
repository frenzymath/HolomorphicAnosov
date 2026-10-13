import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith
import HolomorphicAnosov.Dynamics.ProperRelativeMarkovPartitionG7
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.HomeomorphPowCoe

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter

open Set Filter _root_.Topology
open scoped BigOperators ENNReal Classical
noncomputable section

/-- The public original closed stable plaque agrees literally with the natural group-power orbit inequality used in the coding provider. This is an equality of unchanged definitions, not of different metrics or radii. -/
theorem stable_plaque_homeomorph_pow {X:Type*}[MetricSpace X]
 (F:X≃ₜX) (γ:ℝ) (x:X) :
 relativeClosedStablePlaque F γ x={y | ∀n:ℕ,dist ((F^n) y) ((F^n) x)≤γ} := by
 simp only [relativeClosedStablePlaque,homeomorph_pow_coe]


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter
