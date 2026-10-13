import HolomorphicAnosov.Topology.CircleSingularCohomologyWinding
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.AdditivePositiveLoopOrientation
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SingularPullbackHomeomorph
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SingularOneSimplexNaturality
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.QuotientMapRepresentative

open CategoryTheory
open scoped Simplicial
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

set_option backward.isDefEq.respectTransparency false in
/-- For the additive unit circle, every rational singular cocycle evaluating to one on the positive quotient loop represents the vector of a singleton basis of degree-one cohomology.

Source: Hatcher, Algebraic Topology, circle cohomology pp197–201 and positive winding normalization Theorem 2A.1 pp166–167; Mathlib AddCircle.homeomorphCircle.

Pull the cocycle through the inverse of the oriented circle homeomorphism. Naturality of singular simplices sends the positive complex-circle chain to the specified positive quotient chain, so the pulled cocycle evaluates to one. Uniqueness of the normalized complex-circle class identifies it with its basis vector. Map the basis back along the homeomorphism and use quotient-map functoriality and the inverse law. -/
theorem additive_circle_normalized_basis
    (a : SingularCochain.cycles ℚ (SingularCochain.complex ℚ (TopCat.of UnitAddCircle)) 1)
    (z : LinearMap.ker (((SingularCochain.chainFunctor ℚ).obj (TopCat.of UnitAddCircle)).sc 1).g.hom)
    (hz : z.val = ((TopCat.toSSet.obj (TopCat.of UnitAddCircle)).ιChainComplex
      (R := ModuleCat.of ℚ ℚ) (TopCat.toSSetObj₁Equiv.symm additivePositiveLoop)) 1)
    (hnorm : (show ((SingularCochain.chainFunctor ℚ).obj (TopCat.of UnitAddCircle)).X 1 ⟶
      ModuleCat.of ℚ ℚ from a.val) z.val = 1) :
    ∃ B : Module.Basis Unit ℚ
    (SingularCochain.cohomology ℚ (TopCat.of UnitAddCircle) 1),
    B () = SingularCochain.cocycleClass ℚ
      (SingularCochain.complex ℚ (TopCat.of UnitAddCircle)) 1 a := by
  classical
  obtain ⟨zc, ac₀, uc, up, B₁, Bc1, Bc0, Bp, hz₀, hB₁, hBc1, hBc0,
      hBp, hu, hup, hEval₀, huniq, hz₂, hzp, hconst, hsq⟩ :=
    CircleSingularCohomology.circle_singular_cohomology_winding ℚ
  let e : UnitAddCircle ≃ₜ Circle :=
    AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  let g : CircleSingularCohomology.circleSpace ⟶ TopCat.of UnitAddCircle :=
    (TopCat.isoOfHomeo e).inv
  let ac : SingularCochain.cycles ℚ
      (SingularCochain.complex ℚ CircleSingularCohomology.circleSpace) 1 :=
    ⟨(SingularCochain.pullback ℚ g).f 1 a.val,
      FieldChainKronecker.map_cycle_mem (SingularCochain.pullback ℚ g) 1 a⟩
  have hinv : CircleSingularCohomology.positiveLoop ≫ g = additivePositiveLoop := by
    rw [← additivePositiveLoop_orientation]
    dsimp [g, e]
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hchain : (((SingularCochain.chainFunctor ℚ).map g).f 1) zc.val = z.val := by
    rw [hz, hz₀]
    have he : (TopCat.toSSet.obj CircleSingularCohomology.circleSpace).ιChainComplex
        (R := ModuleCat.of ℚ ℚ) CircleSingularCohomology.positiveSimplex ≫
        (((SingularCochain.chainFunctor ℚ).map g).f 1) =
        (TopCat.toSSet.obj (TopCat.of UnitAddCircle)).ιChainComplex
          (R := ModuleCat.of ℚ ℚ)
          (TopCat.toSSetObj₁Equiv.symm additivePositiveLoop) := by
      change _ ≫ (SSet.chainComplexMap (TopCat.toSSet.map g)
        (ModuleCat.of ℚ ℚ)).f 1 = _
      rw [SSet.ι_chainComplexMap_f, CircleSingularCohomology.positiveSimplex,
        singularOneSimplex_naturality]
      exact congrArg (fun σ ↦ (TopCat.toSSet.obj (TopCat.of UnitAddCircle)).ιChainComplex
        (R := ModuleCat.of ℚ ℚ) σ)
        (congrArg TopCat.toSSetObj₁Equiv.symm hinv)
    exact congrArg (fun t ↦ t (1 : ℚ)) he
  have hEval : CircleSingularCohomology.cocycleEval ℚ
      CircleSingularCohomology.circleSpace 1 ac zc.val = 1 := by
    change (show ((SingularCochain.chainFunctor ℚ).obj
      (TopCat.of UnitAddCircle)).X 1 ⟶ ModuleCat.of ℚ ℚ from a.val)
      ((((SingularCochain.chainFunctor ℚ).map g).f 1) zc.val) = 1
    rw [hchain]
    exact hnorm
  have hclass := huniq ac hEval
  let E := singularPullbackHomeomorph
    (X := TopCat.of UnitAddCircle) (Y := CircleSingularCohomology.circleSpace) e 1
  have hac : SingularCochain.cocycleClass ℚ
      (SingularCochain.complex ℚ CircleSingularCohomology.circleSpace) 1 ac =
      E.symm (SingularCochain.cocycleClass ℚ
        (SingularCochain.complex ℚ (TopCat.of UnitAddCircle)) 1 a) :=
    (quotient_map_representative (SingularCochain.pullback ℚ g) 1 a ac rfl).symm
  refine ⟨Bc1.map E, ?_⟩
  rw [Module.Basis.map_apply, hBc1, ← hclass]
  exact (congrArg E hac).trans (E.apply_symm_apply _)

end HolomorphicAnosov.TorusRationalCupBasisKronecker
