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

/-- The native homeomorphism group power is exactly iteration of its underlying function. This is the required public closed-plaque function/group coercion identity. -/
theorem homeomorph_pow_coe {X:Type*}[TopologicalSpace X]
 (F:X≃ₜX)(n:ℕ) :
 ((F^n : X≃ₜX) : X→X)=(F:X→X)^[n] := by
 exact hom_coe_pow (fun g : X ≃ₜ X ↦ (g : X → X)) rfl (fun _ _ ↦ rfl) F n


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter
