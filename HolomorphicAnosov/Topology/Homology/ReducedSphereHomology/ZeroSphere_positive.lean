import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.ZeroSphere_discrete
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.IntegralReducedPositiveOrdinaryIso

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

/-- Hatcher's off-top S⁰ calculation is the actual totally disconnected
singular-chain calculation, transported through the augmentation shift. -/
theorem zeroSphere_positive (n : ℕ) :
    IsZero (integralReducedSingularHomology
      (TopCat.of {x : EuclideanSpace ℝ (Fin 1) // ‖x‖ = 1}) (n + 1)) := by
  let S := {x : EuclideanSpace ℝ (Fin 1) // ‖x‖ = 1}
  let : DiscreteTopology S := zeroSphere_discrete
  apply IsZero.of_iso ?_ (integralReducedPositiveOrdinaryIso (TopCat.of S) n)
  exact AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat ℤ) (n + 1) reducedSingularIntegralCoefficients (TopCat.of S) (by omega)

end HolomorphicAnosov.Topology.Homology
