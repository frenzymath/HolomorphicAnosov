import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Limits
open CategoryTheory CategoryTheory.Limits Opposite
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain
set_option backward.isDefEq.respectTransparency false
/-- Source: Hatcher, Algebraic Topology, pp.201–202.

The R-linear Yoneda functor preserves limits: after applying the forgetful functor to types it is ordinary representable Yoneda, which preserves limits, and the forgetful functor reflects limits. Degreewise application to complexes preserves finite limits, as does the opposite-complex equivalence. A cokernel cofork becomes a limiting kernel fork in the opposite category. Apply the dual functor to this fork and its limit proof, and compare the resulting limiting fork with the chosen categorical kernel. Uniqueness of limits supplies the isomorphism, and its cone-morphism equation supplies the inclusion formula. -/
theorem cochain_dual_cokernel_iso (R : Type u) [CommRing R]
    {C D Q : ChainComplex (ModuleCat.{u} R) ℕ} (f : C ⟶ D) (p : D ⟶ Q)
    (w : f ≫ p = 0) (h : IsColimit (CokernelCofork.ofπ p w)) :
    ∃ e : (dualFunctor R).obj (op Q) ≅ kernel ((dualFunctor R).map f.op),
      e.hom ≫ kernel.ι ((dualFunctor R).map f.op) = (dualFunctor R).map p.op := by
  let F := (linearYoneda R (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  have : PreservesLimits (F ⋙ forget (ModuleCat.{u} R)) :=
    (inferInstance : PreservesLimits (yoneda.obj (ModuleCat.of R R)))
  have : PreservesLimits F := preservesLimits_of_reflects_of_preserves F (forget _)
  have : PreservesFiniteLimits (dualFunctor R) := by dsimp [dualFunctor]; infer_instance
  let hk := CokernelCofork.IsColimit.ofπOp p w h
  let hm := isLimitForkMapOfIsLimit' (dualFunctor R) _ hk
  refine ⟨hm.conePointUniqueUpToIso (limit.isLimit _), ?_⟩
  exact hm.conePointUniqueUpToIso_hom_comp (limit.isLimit _) WalkingParallelPair.zero
end HolomorphicAnosov.SingularCochain

