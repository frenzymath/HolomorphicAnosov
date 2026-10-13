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

attribute [-instance] AddCommGroup.toIntModule in
/-- The actual two-point zero-chain module is the direct sum of two copies
of its coefficient module, expressed through its coproduct universal property. -/
def boolCoproductIso (R : ModuleCat ℤ) :
    (∐ fun _ : Bool ↦ R) ≅ ModuleCat.of ℤ (R × R) where
  hom := Sigma.desc (fun b ↦ ModuleCat.ofHom
    (if b then LinearMap.inr ℤ R R else LinearMap.inl ℤ R R))
  inv := ModuleCat.ofHom
    (((Sigma.ι (fun _ : Bool ↦ R) false).hom).comp (LinearMap.fst ℤ R R) +
      ((Sigma.ι (fun _ : Bool ↦ R) true).hom).comp (LinearMap.snd ℤ R R))
  hom_inv_id := by
    apply Sigma.hom_ext
    intro b
    cases b <;> ext x <;> simp
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rcases x with ⟨a, b⟩
    simp

end HolomorphicAnosov.Topology.Homology
