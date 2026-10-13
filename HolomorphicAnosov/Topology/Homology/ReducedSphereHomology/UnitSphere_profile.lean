import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.ZeroSphere_positive
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.SphereProfile_induction
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.ZeroSphere_degreeZeroIso
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.UnitSphere_successor

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

/-- Hatcher's disk-pair induction now applies to the exact original sphere
family in every nonnegative degree, including its two-point base case. -/
theorem unitSphere_profile (k : ℕ) :
    Nonempty (integralReducedSingularHomology
      (TopCat.of {x : EuclideanSpace ℝ (Fin (k + 1)) // ‖x‖ = 1}) k ≅
      reducedSingularIntegralCoefficients) ∧
    ∀ q, q ≠ k → IsZero (integralReducedSingularHomology
      (TopCat.of {x : EuclideanSpace ℝ (Fin (k + 1)) // ‖x‖ = 1}) q) := by
  apply sphereProfile_induction
    (fun k q ↦ integralReducedSingularHomology
      (TopCat.of {x : EuclideanSpace ℝ (Fin (k + 1)) // ‖x‖ = 1}) q)
    reducedSingularIntegralCoefficients
  · exact ⟨zeroSphere_degreeZeroIso⟩
  · intro q hq
    cases q with
    | zero => exact (hq rfl).elim
    | succ n => exact zeroSphere_positive n
  · intro k
    exact (unitSphere_successor k).1
  · intro k q
    exact (unitSphere_successor k).2 q

end HolomorphicAnosov.Topology.Homology
