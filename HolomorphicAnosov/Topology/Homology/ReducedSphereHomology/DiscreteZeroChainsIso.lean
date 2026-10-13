import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

/-- Degree-zero chains of a totally disconnected space are the free
integer coefficient coproduct indexed by its actual points. The isomorphism
comes from the singular-set constant equivalence, not an assumed homology
calculation. -/
def discreteZeroChainsIso (X : TopCat) [TotallyDisconnectedSpace X] :
    ((TopCat.toSSet.obj X).chainComplex reducedSingularIntegralCoefficients).X 0 ≅
      ∐ fun _ : X ↦ reducedSingularIntegralCoefficients :=
  (sigmaConst.obj reducedSingularIntegralCoefficients).mapIso
    ((TopCat.toSSetIsoConst X).app (Opposite.op (SimplexCategory.mk 0)))

end HolomorphicAnosov.Topology.Homology
