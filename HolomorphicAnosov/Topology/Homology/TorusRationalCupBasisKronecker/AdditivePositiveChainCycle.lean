import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.AdditivePositiveLoop

open CategoryTheory
open scoped Simplicial
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

/-- The positive additive loop defines an actual cycle in the original singular chain complex;
the two endpoint faces agree modulo the unit lattice. -/
theorem additivePositiveChain_cycle :
    ((TopCat.toSSet.obj (TopCat.of UnitAddCircle)).ιChainComplex
      (R := ModuleCat.of ℚ ℚ) (TopCat.toSSetObj₁Equiv.symm additivePositiveLoop)) 1 ∈
    LinearMap.ker (((SingularCochain.chainFunctor ℚ).obj
      (TopCat.of UnitAddCircle)).sc 1).g.hom := by
  let S := TopCat.toSSet.obj (TopCat.of UnitAddCircle)
  let σ := TopCat.toSSetObj₁Equiv.symm additivePositiveLoop
  have hd : S.ιChainComplex (R := ModuleCat.of ℚ ℚ) σ ≫
      (S.chainComplex (ModuleCat.of ℚ ℚ)).d 1 0 =
      ∑ i : Fin 2, (-1 : ℤ) ^ i.val • S.ιChainComplex (S.δ i σ) :=
    SSet.ιChainComplex_d S (R := ModuleCat.of ℚ ℚ) σ
  have he : S.δ 0 σ = S.δ 1 σ := by
    dsimp [S, σ]
    rw [TopCat.δ_zero_toSSetObj₁Equiv.symm, TopCat.δ_one_toSSetObj₁Equiv.symm]
    congr 1
    change ((1 : ℝ) : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle)
    simp
  rw [Fin.sum_univ_two] at hd
  have hd' : S.ιChainComplex (R := ModuleCat.of ℚ ℚ) σ ≫
      (S.chainComplex (ModuleCat.of ℚ ℚ)).d 1 0 = 0 := by
    simpa only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul,
      neg_one_zsmul, he, add_neg_cancel] using hd
  have hd0 : ((S.chainComplex (ModuleCat.of ℚ ℚ)).d 1 0)
      ((S.ιChainComplex (R := ModuleCat.of ℚ ℚ) σ) 1) = 0 :=
    congrArg (fun t ↦ t (1 : ℚ)) hd'
  change (((SingularCochain.chainFunctor ℚ).obj (TopCat.of UnitAddCircle)).dFrom 1)
    ((S.ιChainComplex (R := ModuleCat.of ℚ ℚ) σ) 1) = 0
  rw [HomologicalComplex.dFrom_eq _ (show (ComplexShape.down ℕ).Rel 1 0 from rfl)]
  change ((HomologicalComplex.xNextIso
    ((SingularCochain.chainFunctor ℚ).obj (TopCat.of UnitAddCircle))
      (show (ComplexShape.down ℕ).Rel 1 0 from rfl)).inv)
        (((S.chainComplex (ModuleCat.of ℚ ℚ)).d 1 0)
          ((S.ιChainComplex (R := ModuleCat.of ℚ ℚ) σ) 1)) = 0
  exact (congrArg (fun z ↦ (HomologicalComplex.xNextIso
    ((SingularCochain.chainFunctor ℚ).obj (TopCat.of UnitAddCircle))
      (show (ComplexShape.down ℕ).Rel 1 0 from rfl)).inv z) hd0).trans (map_zero _)

end HolomorphicAnosov.TorusRationalCupBasisKronecker
