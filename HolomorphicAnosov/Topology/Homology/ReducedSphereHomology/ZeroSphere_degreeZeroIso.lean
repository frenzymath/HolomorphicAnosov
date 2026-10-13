import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.BoolSumKernelIso
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.DiscreteReducedH0SumKernel
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.ZeroSphereBoolHomeomorph
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.ReducedHomologyHomeomorphIso

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

/-- Complete reduced degree-zero computation of the actual S⁰, using its
native homeomorphism to the two-point space and the augmented coefficient sum. -/
def zeroSphere_degreeZeroIso :
    integralReducedSingularHomology
      (TopCat.of {x : EuclideanSpace ℝ (Fin 1) // ‖x‖ = 1}) 0 ≅
        reducedSingularIntegralCoefficients :=
  reducedHomologyHomeomorphIso zeroSphereBoolHomeomorph 0 ≪≫
    discreteReducedH0SumKernel (TopCat.of Bool) ≪≫
    boolSumKernelIso reducedSingularIntegralCoefficients

end HolomorphicAnosov.Topology.Homology
