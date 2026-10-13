import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SingularOneSimplexNaturality
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SingularPullbackComp
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.QuotientMapRepresentative
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.AdditivePositiveLoop
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.AdditivePositiveLoopOrientation
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.AdditivePositiveChainCycle

open CategoryTheory
open scoped Simplicial
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

set_option backward.isDefEq.respectTransparency false in
/-- The source circle cocycle transported along the orientation-fixed quotient homeomorphism
normalizes the literal positive additive loop, which is an actual singular cycle. -/
theorem additive_circle_normalization :
    ∃ (a : SingularCochain.cycles ℚ
          (SingularCochain.complex ℚ (TopCat.of UnitAddCircle)) 1)
      (z : LinearMap.ker (((SingularCochain.chainFunctor ℚ).obj
        (TopCat.of UnitAddCircle)).sc 1).g.hom),
      z.val = ((TopCat.toSSet.obj (TopCat.of UnitAddCircle)).ιChainComplex
        (R := ModuleCat.of ℚ ℚ) (TopCat.toSSetObj₁Equiv.symm additivePositiveLoop)) 1 ∧
      (show ((SingularCochain.chainFunctor ℚ).obj (TopCat.of UnitAddCircle)).X 1 ⟶
        ModuleCat.of ℚ ℚ from a.val) z.val = 1 ∧
      (∀ (Z : TopCat) (b : UnitAddCircle),
        (SingularCochain.cohomologyPullback ℚ
          (TopCat.ofHom (ContinuousMap.const Z b)) 1)
          (SingularCochain.cocycleClass ℚ
            (SingularCochain.complex ℚ (TopCat.of UnitAddCircle)) 1 a) = 0) := by
  obtain ⟨zc, ac, uc, up, B₁, Bc1, Bc0, Bp, hz, hrest⟩ :=
    CircleSingularCohomology.circle_singular_cohomology_winding ℚ
  have hae := hrest.2.2.2.2.2.2.1
  let f : TopCat.of UnitAddCircle ⟶ CircleSingularCohomology.circleSpace := (TopCat.isoOfHomeo (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero)).hom
  let a : SingularCochain.cycles ℚ
      (SingularCochain.complex ℚ (TopCat.of UnitAddCircle)) 1 :=
    ⟨(SingularCochain.pullback ℚ f).f 1 ac.val,
      FieldChainKronecker.map_cycle_mem (SingularCochain.pullback ℚ f) 1 ac⟩
  let z : LinearMap.ker (((SingularCochain.chainFunctor ℚ).obj
      (TopCat.of UnitAddCircle)).sc 1).g.hom := ⟨_, additivePositiveChain_cycle⟩
  refine ⟨a, z, rfl, ?_, ?_⟩
  · change (show ((SingularCochain.chainFunctor ℚ).obj
      CircleSingularCohomology.circleSpace).X 1 ⟶ ModuleCat.of ℚ ℚ from ac.val)
        ((((SingularCochain.chainFunctor ℚ).map f).f 1) z.val) = 1
    have hmap : (((SingularCochain.chainFunctor ℚ).map f).f 1) z.val = zc.val := by
      rw [hz]
      have he : (TopCat.toSSet.obj (TopCat.of UnitAddCircle)).ιChainComplex
          (R := ModuleCat.of ℚ ℚ) (TopCat.toSSetObj₁Equiv.symm additivePositiveLoop) ≫
          (((SingularCochain.chainFunctor ℚ).map f).f 1) =
        (TopCat.toSSet.obj CircleSingularCohomology.circleSpace).ιChainComplex
          (R := ModuleCat.of ℚ ℚ) CircleSingularCohomology.positiveSimplex := by
        change _ ≫ (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)).f 1 = _
        rw [SSet.ι_chainComplexMap_f, singularOneSimplex_naturality]
        exact congrArg (fun σ ↦ (TopCat.toSSet.obj CircleSingularCohomology.circleSpace).ιChainComplex
          (R := ModuleCat.of ℚ ℚ) σ)
          (congrArg TopCat.toSSetObj₁Equiv.symm additivePositiveLoop_orientation)
      exact congrArg (fun t ↦ t (1 : ℚ)) he
    rw [hmap]
    exact hae

  · intro Z b
    have hpa : SingularCochain.cocycleClass ℚ
        (SingularCochain.complex ℚ (TopCat.of UnitAddCircle)) 1 a =
        (SingularCochain.cohomologyPullback ℚ f 1)
          (SingularCochain.cocycleClass ℚ
            (SingularCochain.complex ℚ CircleSingularCohomology.circleSpace) 1 ac) :=
      (quotient_map_representative (SingularCochain.pullback ℚ f) 1 ac a rfl).symm
    rw [hpa, ← ConcreteCategory.comp_apply, ← singularPullback_comp]
    have he : TopCat.ofHom (ContinuousMap.const Z b) ≫ f =
        TopCat.ofHom (ContinuousMap.const Z (f b)) := rfl
    rw [he]
    exact hrest.2.2.2.2.2.2.2.2.2.2.1 Z (f b)

end HolomorphicAnosov.TorusRationalCupBasisKronecker
