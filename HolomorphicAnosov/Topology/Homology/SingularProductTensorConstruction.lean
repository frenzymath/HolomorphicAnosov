import HolomorphicAnosov.Topology.Homology.SingularProductGeneratorExtension
import HolomorphicAnosov.Topology.Homology.LiftedSingularCone
import HolomorphicAnosov.Topology.Homology.NaturalComparisonInduction
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed

/-! Bredon's product-to-tensor comparison construction, VI1.2–1.3,
pp.316–318, with the degree-zero normalization retained. -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped Simplicial TensorProduct
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace HolomorphicAnosov.SingularProductTensor
open SingularProductGenerator
variable (R : Type u) [CommRing R]

abbrev tensorChains := ((chains R).prod (chains R)) ⋙
  tensor (ChainComplex (ModuleCat.{u} R) ℕ)

/-- Tensor of two degree-zero simplex generators, included in total degree zero. -/
def generator (X : TopCat.{u} × TopCat.{u})
    (σ : (TopCat.toSSet.obj X.1).obj (.op ⦋0⦌))
    (τ : (TopCat.toSSet.obj X.2).obj (.op ⦋0⦌)) :
    coeff R ⟶ ((tensorChains R).obj X).X 0 :=
  (λ_ (coeff R)).inv ≫
    ((TopCat.toSSet.obj X.1).ιChainComplex σ ⊗ₘ
      (TopCat.toSSet.obj X.2).ιChainComplex τ) ≫
    HomologicalComplex.ιTensorObj ((chains R).obj X.1) ((chains R).obj X.2) 0 0 0 rfl

lemma ι_tensor_map {K L K' L' : ChainComplex (ModuleCat.{u} R) ℕ}
    (f : K ⟶ K') (g : L ⟶ L') (p q n : ℕ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj K L p q n h ≫
      (HomologicalComplex.tensorHom f g).f n =
    (f.f p ⊗ₘ g.f q) ≫ HomologicalComplex.ιTensorObj K' L' p q n h := by
  simpa only [HomologicalComplex.tensorHom, HomologicalComplex.ιTensorObj,
    curriedTensor_map_app, curriedTensor_obj_map, tensorHom_def, Category.assoc] using
      HomologicalComplex.ι_mapBifunctorMap f g (curriedTensor (ModuleCat.{u} R))
        (ComplexShape.down ℕ) p q n h

@[reassoc]
lemma generator_naturality (X Y : TopCat.{u} × TopCat.{u}) (f : X ⟶ Y)
    (σ : (TopCat.toSSet.obj X.1).obj (.op ⦋0⦌))
    (τ : (TopCat.toSSet.obj X.2).obj (.op ⦋0⦌)) :
    generator R X σ τ ≫ ((tensorChains R).map f).f 0 =
      generator R Y ((TopCat.toSSet.map f.1).app _ σ) ((TopCat.toSSet.map f.2).app _ τ) := by
  change generator R X σ τ ≫
    (HomologicalComplex.tensorHom ((chains R).map f.1) ((chains R).map f.2)).f 0 = _
  dsimp only [generator]
  rw [Category.assoc, Category.assoc, ι_tensor_map]
  erw [tensorHom_comp_tensorHom_assoc]
  erw [SSet.ι_chainComplexMap_f, SSet.ι_chainComplexMap_f]

/-- The normalized degree-zero product comparison. -/
def zero : (chainComplexOfFunctor (productChains R)).X 0 ⟶
    (chainComplexOfFunctor (tensorChains R)).X 0 :=
  extend R 0 _ (generator R (model 0) (ULift.up (𝟙 _)) (ULift.up (𝟙 _)))

@[reassoc]
lemma ι_zero (X : TopCat.{u} × TopCat.{u})
    (σ : (TopCat.toSSet.obj (X.1 ⊗ X.2)).obj (.op ⦋0⦌)) :
    (TopCat.toSSet.obj (X.1 ⊗ X.2)).ιChainComplex σ ≫ (zero R).app X =
      generator R X (ULift.up (generatorMap σ).1) (ULift.up (generatorMap σ).2) := by
  change _ ≫ extendApp R 0 _ _ X = _
  erw [ι_extendApp]
  change generator R (model 0) _ _ ≫ ((tensorChains R).map (generatorMap σ)).f 0 = _
  rw [generator_naturality]
  rfl

/-- A chosen vertex in the lifted standard simplex. -/
def modelPoint (n : ℕ) : LiftedSingularCone.space.{u} (.simplex n) :=
  Classical.choice (inferInstance : Nonempty (SimplexCategory.toTop.obj ⦋n⦌))

/-- Positive tensor-model cycles have natural fillings for every source degree.
Source: Bredon VI1.2–1.3. Evaluate on the diagonal model, compose with the
tensor cone contraction, and use the free extension theorem. -/
theorem fill_positive (k n : ℕ)
    (r : (chainComplexOfFunctor (productChains R)).X k ⟶
      (chainComplexOfFunctor (tensorChains R)).X (n + 1))
    (hr : r ≫ (chainComplexOfFunctor (tensorChains R)).d (n + 1) n = 0) :
    ∃ s : (chainComplexOfFunctor (productChains R)).X k ⟶
      (chainComplexOfFunctor (tensorChains R)).X (n + 2),
      s ≫ (chainComplexOfFunctor (tensorChains R)).d (n + 2) (n + 1) = r := by
  refine lift_natural R k _ _
    ((chainComplexOfFunctor (tensorChains R)).d (n + 2) (n + 1)) r ?_
  let v := (TopCat.toSSet.obj ((model k).1 ⊗ (model k).2)).ιChainComplex
    (R := coeff R) (diagonal k) ≫ r.app (model k)
  have hv : v ≫ ((tensorChains R).obj (model k)).d (n + 1) n = 0 := by
    have h := NatTrans.congr_app hr (model k)
    dsimp only [NatTrans.comp_app, zero_app, chainComplexOfFunctor] at h
    dsimp [v]
    erw [Category.assoc, h, comp_zero]
  exact ⟨v ≫ (LiftedSingularCone.tensorContraction R (.simplex k) (.simplex k)
    (modelPoint k) (modelPoint k)).hom (n + 1) (n + 2),
    LiftedSingularCone.tensor_fill_positive R (.simplex k) (.simplex k)
      (modelPoint k) (modelPoint k) n v hv⟩

lemma generator_epsilon (k : ℕ)
    (σ τ : (TopCat.toSSet.obj (model.{u} k).1).obj (.op ⦋0⦌)) :
    generator R (model k) σ τ ≫
      (HomologicalComplex.tensorHom
        (LiftedSingularCone.epsilon R (.simplex k) (modelPoint k))
        (LiftedSingularCone.epsilon R (.simplex k) (modelPoint k))).f 0 =
      generator R (model k)
        (LiftedSingularCone.baseGenerator (.simplex k) (modelPoint k))
        (LiftedSingularCone.baseGenerator (.simplex k) (modelPoint k)) := by
  dsimp only [generator]
  rw [Category.assoc, Category.assoc, ι_tensor_map]
  erw [tensorHom_comp_tensorHom_assoc]
  erw [LiftedSingularCone.ι_epsilon_zero, LiftedSingularCone.ι_epsilon_zero]
  rfl

/-- The degree-one boundary residual has zero tensor augmentation.
Source: Bredon VI1.3, p.317. Its two boundary vertices both map to the tensor
of base points after augmentation, so the alternating pair cancels. -/
theorem first_boundary_augmentation :
    ((TopCat.toSSet.obj ((model 1).1 ⊗ (model 1).2)).ιChainComplex
      (R := coeff R) (diagonal 1) ≫
      ((productChains R).obj (model 1)).d 1 0 ≫ (zero R).app (model 1)) ≫
      (HomologicalComplex.tensorHom
        (LiftedSingularCone.epsilon R (.simplex 1) (modelPoint 1))
        (LiftedSingularCone.epsilon R (.simplex 1) (modelPoint 1))).f 0 = 0 := by
  erw [← Category.assoc, SSet.ιChainComplex_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc]
  erw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.sum_univ_one]
  erw [ι_zero_assoc R (model 1), ι_zero_assoc R (model 1),
    generator_epsilon R 1, generator_epsilon R 1]
  simp

/-- The first comparison component is filled on the one-simplex model. -/
theorem exists_one :
    ∃ one : (chainComplexOfFunctor (productChains R)).X 1 ⟶
        (chainComplexOfFunctor (tensorChains R)).X 1,
      one ≫ (chainComplexOfFunctor (tensorChains R)).d 1 0 =
        (chainComplexOfFunctor (productChains R)).d 1 0 ≫ zero R := by
  refine lift_natural R 1 _ _ ((chainComplexOfFunctor (tensorChains R)).d 1 0)
    ((chainComplexOfFunctor (productChains R)).d 1 0 ≫ zero R) ?_
  let v := (TopCat.toSSet.obj ((model 1).1 ⊗ (model 1).2)).ιChainComplex
    (R := coeff R) (diagonal 1) ≫
      ((productChains R).obj (model 1)).d 1 0 ≫ (zero R).app (model 1)
  exact ⟨v ≫ (LiftedSingularCone.tensorContraction R (.simplex 1) (.simplex 1)
    (modelPoint 1) (modelPoint 1)).hom 0 1,
    LiftedSingularCone.tensor_fill_zero R (.simplex 1) (.simplex 1)
      (modelPoint 1) (modelPoint 1) v (first_boundary_augmentation R)⟩

/-- Existence of the product-to-tensor comparison with its fixed degree-zero map.
Source: Bredon VI1.2–1.3, pp.316–318. The first residual is augmentation-zero;
all later residuals are positive cycles. The model fillings extend naturally,
so the generic induction applies in the category of functors. -/
theorem exists_comparison :
    ∃ θ : productChains R ⟶ tensorChains R, ∀ X, (θ.app X).f 0 = (zero R).app X := by
  obtain ⟨one, hone⟩ := exists_one R
  obtain ⟨θ, hθ, _⟩ := chain_comparison_induction
    (chainComplexOfFunctor (productChains R)) (chainComplexOfFunctor (tensorChains R))
    (zero R) one hone (fun n r hr ↦ fill_positive R (n + 2) n r hr)
  exact ⟨naturalTransformationOfChainMap θ, fun X ↦ NatTrans.congr_app hθ X⟩

/-- Normalized natural comparisons are naturally homotopic relative to degree zero.
Source: Bredon VI1.2–1.3, pp.316–318. Naturality at point inclusions gives
equality of the zero components. The generic residual homotopy induction then
uses the positive tensor-model fillings in every higher degree. -/
theorem unique_comparison (Φ Ψ : productChains R ⟶ tensorChains R)
    (h : (TopCat.toSSet.obj (point ⊗ point)).ιChainComplex pointSimplex ≫
        (Φ.app pointPair).f 0 =
      (TopCat.toSSet.obj (point ⊗ point)).ιChainComplex pointSimplex ≫
        (Ψ.app pointPair).f 0) :
    ∃ H : ∀ X, _root_.Homotopy (Φ.app X) (Ψ.app X),
      (∀ X Y (f : X ⟶ Y) (i j : ℕ),
        ((productChains R).map f).f i ≫ (H Y).hom i j =
          (H X).hom i j ≫ ((tensorChains R).map f).f j) ∧
      (∀ X, (H X).hom 0 1 = 0) := by
  apply barr_natural_relative_homotopy
  · intro X
    exact NatTrans.congr_app (zero_eq_of_point R _
      ((chainMapOfNaturalTransformation Φ).f 0)
      ((chainMapOfNaturalTransformation Ψ).f 0) h) X
  · exact fun n r hr ↦ fill_positive R (n + 1) n r hr

end HolomorphicAnosov.SingularProductTensor
