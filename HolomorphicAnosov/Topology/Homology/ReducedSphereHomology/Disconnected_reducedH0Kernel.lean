import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.Disconnected_first_boundary_zero

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

set_option backward.isDefEq.respectTransparency false in
/-- For a totally disconnected space reduced degree zero is the actual kernel
of coefficient sum on zero-chains, since the first singular boundary is zero.
No ordinary H₀ replacement is made. -/
def disconnected_reducedH0Kernel (X : TopCat) [TotallyDisconnectedSpace X] :
    integralReducedSingularHomology X 0 ≅ kernel (integralSingularAugmentation X) := by
  let A := augmentedIntegralSingularChains X
  let S := A.sc' 2 1 0
  have hf : S.f = 0 := by
    exact disconnected_first_boundary_zero X
  exact A.homologyIsoSc' 2 1 0 (by simp) (by simp) ≪≫
    (S.asIsoHomologyπ hf).symm ≪≫ S.cyclesIsoKernel

end HolomorphicAnosov.Topology.Homology
