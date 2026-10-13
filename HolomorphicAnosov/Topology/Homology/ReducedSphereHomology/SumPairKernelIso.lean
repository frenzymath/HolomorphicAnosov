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
/-- The kernel of the two-coordinate sum consists exactly of (a,-a).
This is the augmented degree-zero calculation in Hatcher's two-point base case. -/
def sumPairKernelIso (R : ModuleCat ℤ) :
    kernel (ModuleCat.ofHom ((LinearMap.fst ℤ R R) + (LinearMap.snd ℤ R R))) ≅ R := by
  let l : R × R →ₗ[ℤ] R := LinearMap.fst ℤ R R + LinearMap.snd ℤ R R
  let e : l.ker ≃ₗ[ℤ] R :=
    { toFun := fun x ↦ x.val.1
      invFun := fun a ↦ ⟨(a, -a), by simp [l]⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · have h : x.val.1 + x.val.2 = 0 := by
            change l x.val = 0 at *
            exact x.property
          exact neg_eq_of_add_eq_zero_right h
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact ModuleCat.kernelIsoKer (ModuleCat.ofHom l) ≪≫ e.toModuleIso

end HolomorphicAnosov.Topology.Homology
