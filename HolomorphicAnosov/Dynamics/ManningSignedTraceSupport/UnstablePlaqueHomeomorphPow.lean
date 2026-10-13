import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith
import HolomorphicAnosov.Dynamics.ProperRelativeMarkovPartitionG7
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.HomeomorphZpowNegCoe

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter

open Set Filter _root_.Topology
open scoped BigOperators ENNReal Classical
noncomputable section

/-- The public original closed unstable plaque agrees literally with the negative group-power orbit inequality used in the coding provider. The inverse endpoints and time-zero condition are retained. -/
theorem unstable_plaque_homeomorph_pow {X:Type*}[MetricSpace X]
 (F:X≃ₜX) (γ:ℝ) (x:X) :
 relativeClosedUnstablePlaque F γ x={y | ∀n:ℕ,dist ((F^(-(n:ℤ))) y) ((F^(-(n:ℤ))) x)≤γ} := by
 simp only [relativeClosedUnstablePlaque,homeomorph_zpow_neg_coe]


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter
