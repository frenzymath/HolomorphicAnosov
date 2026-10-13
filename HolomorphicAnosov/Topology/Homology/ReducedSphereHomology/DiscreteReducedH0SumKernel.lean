import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.DiscreteZeroChainsIso_augmentation
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.Disconnected_reducedH0Kernel
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.DiscreteZeroChainsIso

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

/-- The reduced degree-zero kernel is thus the kernel of literal sum on the
actual point-indexed free coefficient module. -/
def discreteReducedH0SumKernel (X : TopCat) [TotallyDisconnectedSpace X] :
    integralReducedSingularHomology X 0 ≅ kernel
      (Sigma.desc (fun _ : X ↦ 𝟙 reducedSingularIntegralCoefficients)) :=
  disconnected_reducedH0Kernel X ≪≫ kernel.mapIso _ _
    (discreteZeroChainsIso X) (Iso.refl _) (by
      simpa using (discreteZeroChainsIso_augmentation X).symm)

end HolomorphicAnosov.Topology.Homology
