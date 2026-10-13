import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.BoolCoproductIso

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

attribute [-instance] AddCommGroup.toIntModule in
/-- The coefficient sum is literal addition in the two coordinates. -/
theorem boolCoproductIso_sum (R : ModuleCat ℤ) :
    (boolCoproductIso R).hom ≫ ModuleCat.ofHom
      ((LinearMap.fst ℤ R R) + (LinearMap.snd ℤ R R)) =
    Sigma.desc (fun _ : Bool ↦ 𝟙 R) := by
  apply Sigma.hom_ext
  intro b
  cases b <;> ext x <;> simp [boolCoproductIso]

end HolomorphicAnosov.Topology.Homology
