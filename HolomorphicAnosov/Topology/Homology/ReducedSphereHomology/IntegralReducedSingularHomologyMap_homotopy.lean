import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.AugmentedIntegralSingularChainsHomotopy

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

/-- Actual augmented singular homology is invariant under an ordinary topological
homotopy, including reduced degree zero; this uses the constructed prism, not an
assumed reduced-homology invariance certificate. -/
theorem integralReducedSingularHomologyMap_homotopy {X Y : TopCat.{u}}
    {f g : X ⟶ Y} (H : TopCat.Homotopy f g) (n : ℕ) :
    integralReducedSingularHomologyMap f n = integralReducedSingularHomologyMap g n :=
  (augmentedIntegralSingularChainsHomotopy H).homologyMap_eq (n + 1)

end HolomorphicAnosov.Topology.Homology
