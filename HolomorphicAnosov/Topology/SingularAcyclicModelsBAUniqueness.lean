import HolomorphicAnosov.Topology.SingularAcyclicModelsBAFreeGeneratorResidualFilling

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped Simplicial

namespace HolomorphicAnosov.Topology

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The normalized tensor-to-product acyclic-model uniqueness theorem.

Source: Bredon, VI Theorem 1.3, pp.317–318; Barr, Chapter 5 §5
Proposition 5.5, p.116. Point inclusions and the tensor generator coproduct
force equality in degree zero. In positive degrees, fill the residual cycle
on each pair of simplex models by the ordinary product cone and extend the
filling naturally by its two simplex maps. Barr's relative induction assembles
these fillers into a natural chain homotopy whose degree-zero component is zero. -/
theorem singular_acyclic_models_BA_case :
    let R := ULift.{u} ℚ
    let coefficient : ModuleCat.{u} R := ModuleCat.of R R
    let C : TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
      (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} R)).obj coefficient
    let A : TopCat.{u} × TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
      tensor TopCat.{u} ⋙ C
    let B : TopCat.{u} × TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
      (C.prod C) ⋙ tensor (ChainComplex (ModuleCat.{u} R) ℕ)
    let point : TopCat.{u} := TopCat.of PUnit.{u + 1}
    let pointPair := (point, point)
    let gA : coefficient ⟶ (A.obj pointPair).X 0 :=
      (TopCat.toSSet.obj (point ⊗ point)).ιChainComplex
        ((TopCat.toSSetObjEquiv (point ⊗ point) (Opposite.op ⦋0⦌)).symm
          (ContinuousMap.const _ (PUnit.unit, PUnit.unit)))
    let gB : coefficient ⟶ (B.obj pointPair).X 0 :=
      (λ_ coefficient).inv ≫
        ((TopCat.toSSet.obj point).ιChainComplex
          ((TopCat.toSSetObjEquiv point (Opposite.op ⦋0⦌)).symm
            (ContinuousMap.const _ PUnit.unit)) ⊗ₘ
          (TopCat.toSSet.obj point).ιChainComplex
            ((TopCat.toSSetObjEquiv point (Opposite.op ⦋0⦌)).symm
              (ContinuousMap.const _ PUnit.unit))) ≫
        HomologicalComplex.ιTensorObj (C.obj point) (C.obj point) 0 0 0 rfl
    let naturalHomotopy := fun
      (Φ Ψ : B ⟶ A) ↦
        ∃ H : ∀ X, _root_.Homotopy (Φ.app X) (Ψ.app X),
          (∀ X Y (f : X ⟶ Y) (i j : ℕ),
            (B.map f).f i ≫ (H Y).hom i j =
              (H X).hom i j ≫ (A.map f).f j) ∧
          (∀ X, (H X).hom 0 1 = 0)
    ∀ (Φ Ψ : B ⟶ A),
      gB ≫ (Φ.app pointPair).f 0 = gA →
      gB ≫ (Ψ.app pointPair).f 0 = gA →
      naturalHomotopy Φ Ψ := by
  dsimp only
  intro Φ Ψ hΦ hΨ
  apply barr_natural_relative_homotopy
  · intro X
    apply NatTrans.congr_app (SingularTensorGenerator.zero_eq_of_point (ULift.{u} ℚ) _
      ((chainMapOfNaturalTransformation Φ).f 0)
      ((chainMapOfNaturalTransformation Ψ).f 0) ?_) X
    apply (cancel_epi (λ_ (ModuleCat.of (ULift.{u} ℚ) (ULift.{u} ℚ))).inv).1
    have hh := hΦ.trans hΨ.symm
    simp only [Category.assoc] at hh
    dsimp only [SingularTensorGenerator.generator]
    simp only [Category.assoc]
    exact hh
  · exact singular_acyclic_models_BA_free_generator_residual_filling


end
end HolomorphicAnosov.Topology
