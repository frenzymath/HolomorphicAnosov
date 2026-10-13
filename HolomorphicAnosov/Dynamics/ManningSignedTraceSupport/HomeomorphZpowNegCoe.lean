import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.HomeomorphPowCoe

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter

open Set Filter _root_.Topology
open scoped BigOperators ENNReal Classical
noncomputable section

/-- The native negative integer power is exactly iteration of the original inverse function. The group inverse and Homeomorph.symm are definitionally the same data. -/
theorem homeomorph_zpow_neg_coe {X:Type*}[TopologicalSpace X]
 (F:X≃ₜX)(n:ℕ) :
 ((F^(-(n:ℤ)) : X≃ₜX) : X→X)=(F.symm:X→X)^[n] := by
 have hp:F^(-(n:ℤ))=(F.symm^n) := by
   change F^(-(n:ℤ))=(F⁻¹^n)
   rw [zpow_neg,zpow_natCast,inv_pow]
 rw [hp,homeomorph_pow_coe]


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter
