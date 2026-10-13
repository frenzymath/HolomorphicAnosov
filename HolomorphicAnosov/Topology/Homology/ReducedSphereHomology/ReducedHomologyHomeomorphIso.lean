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

/-- The specified homeomorphism induces a reduced integral homology
isomorphism through the actual augmented-chain functor. Both morphisms are
literal induced maps, including the augmentation degree. -/
def reducedHomologyHomeomorphIso {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (q : ℕ) :
    integralReducedSingularHomology (TopCat.of X) q ≅
      integralReducedSingularHomology (TopCat.of Y) q :=
  (integralReducedSingularHomologyFunctor q).mapIso (TopCat.isoOfHomeo e)

end HolomorphicAnosov.Topology.Homology
