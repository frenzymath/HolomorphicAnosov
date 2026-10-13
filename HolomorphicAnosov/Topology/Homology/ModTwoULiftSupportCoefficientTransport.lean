import HolomorphicAnosov.Topology.Homology.ModTwoULiftSupportCoefficientTransportProof
namespace HolomorphicAnosov.Topology.Homology
universe u
noncomputable section
/-- Completed coefficient and universe transport. -/
theorem modTwo_ulift_support_coefficient_transport
    (X : Type) [TopologicalSpace X] (A : Set X) (k : ℕ) :
    Nonempty (modTwoSupportHomology
      (ULift.{u} X) {y : ULift.{u} X | y.down ∈ A} k ≃ₗ[ZMod 2]
      modTwoSupportHomology X A k) := by
  exact modTwo_ulift_support_coefficient_transport_proved X A k
end
end HolomorphicAnosov.Topology.Homology
