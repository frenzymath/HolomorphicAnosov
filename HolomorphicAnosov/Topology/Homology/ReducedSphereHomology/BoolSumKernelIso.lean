import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.BoolCoproductIso
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.SumPairKernelIso
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.BoolCoproductIso_sum

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

attribute [-instance] AddCommGroup.toIntModule in
def boolSumKernelIso (R : ModuleCat ℤ) :
    kernel (Sigma.desc (fun _ : Bool ↦ 𝟙 R)) ≅ R :=
  kernel.mapIso _ _ (boolCoproductIso R) (Iso.refl _)
    (by simpa using (boolCoproductIso_sum R).symm) ≪≫ sumPairKernelIso R

end HolomorphicAnosov.Topology.Homology
