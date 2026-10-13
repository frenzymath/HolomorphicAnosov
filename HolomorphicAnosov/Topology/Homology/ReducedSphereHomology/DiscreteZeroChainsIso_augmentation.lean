import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.DiscreteZeroChainsIso

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

/-- The zero-chain coordinate change preserves actual coefficient sum on
EVERY singular zero-simplex. -/
theorem discreteZeroChainsIso_augmentation (X : TopCat)
    [TotallyDisconnectedSpace X] :
    (discreteZeroChainsIso X).hom ≫ Sigma.desc
      (fun _ : X ↦ 𝟙 reducedSingularIntegralCoefficients) = integralSingularAugmentation X := by
  apply SSet.chainComplex_hom_ext
  intro σ
  simp [discreteZeroChainsIso, sigmaConst, SSet.ιChainComplex, integralSingularAugmentation]

end HolomorphicAnosov.Topology.Homology
