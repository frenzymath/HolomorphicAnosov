import HolomorphicAnosov.Topology.Homology.SingularProductTensorConstruction
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.Algebra.Field.ULift
import Mathlib.CategoryTheory.Monoidal.Closed.Braided

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped Simplicial
noncomputable section
set_option maxHeartbeats 200000
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HolomorphicAnosov.SingularTensorGenerator
open SingularProductGenerator
variable (R : Type u) [CommRing R]

abbrev tensorChains := SingularProductTensor.tensorChains R

/-- Extend prescribed values on pairs of simplex generators by the two coproducts. -/
@[irreducible]
def extendPair (X Y : TopCat.{u}) (p q : ℕ) (V : ModuleCat.{u} R)
    (v : ∀ _σ : (TopCat.toSSet.obj X).obj (.op ⦋p⦌),
      ∀ _τ : (TopCat.toSSet.obj Y).obj (.op ⦋q⦌), coeff R ⊗ coeff R ⟶ V) :
    ((chains R).obj X).X p ⊗ ((chains R).obj Y).X q ⟶ V := by
  let hc := (TopCat.toSSet.obj X).isColimitChainComplexXCofan (coeff R) p
  let hd := (TopCat.toSSet.obj Y).isColimitChainComplexXCofan (coeff R) q
  let hc' := isColimitCofanMkObjOfIsColimit
    (tensorRight (((chains R).obj Y).X q)) _ _ hc
  let hd' := isColimitCofanMkObjOfIsColimit (tensorLeft (coeff R)) _ _ hd
  exact hc'.desc (Cofan.mk _ (fun σ ↦ hd'.desc (Cofan.mk _ (v σ))))

@[reassoc (attr := simp)]
lemma pair_extendPair (X Y : TopCat.{u}) (p q : ℕ) (V : ModuleCat.{u} R)
    (v : ∀ _σ : (TopCat.toSSet.obj X).obj (.op ⦋p⦌),
      ∀ _τ : (TopCat.toSSet.obj Y).obj (.op ⦋q⦌), coeff R ⊗ coeff R ⟶ V)
    (σ : (TopCat.toSSet.obj X).obj (.op ⦋p⦌))
    (τ : (TopCat.toSSet.obj Y).obj (.op ⦋q⦌)) :
    ((TopCat.toSSet.obj X).ιChainComplex σ ⊗ₘ
      (TopCat.toSSet.obj Y).ιChainComplex τ) ≫ extendPair R X Y p q V v = v σ τ := by
  let hc := isColimitCofanMkObjOfIsColimit
    (tensorRight (((chains R).obj Y).X q)) _ _
    ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (coeff R) p)
  let hd := isColimitCofanMkObjOfIsColimit (tensorLeft (coeff R)) _ _
    ((TopCat.toSSet.obj Y).isColimitChainComplexXCofan (coeff R) q)
  let w := fun σ ↦ hd.desc (Cofan.mk _ (v σ))
  have hσ : ((TopCat.toSSet.obj X).ιChainComplex σ ▷ (((chains R).obj Y).X q)) ≫
      extendPair R X Y p q V v = w σ := by
    unfold extendPair
    exact hc.fac (Cofan.mk _ w) (Discrete.mk σ)
  rw [tensorHom_def', Category.assoc]
  erw [hσ]
  exact hd.fac (Cofan.mk _ (v σ)) (Discrete.mk τ)

lemma pair_hom_ext (X Y : TopCat.{u}) (p q : ℕ) {V : ModuleCat.{u} R}
    {f g : ((chains R).obj X).X p ⊗ ((chains R).obj Y).X q ⟶ V}
    (h : ∀ σ τ, ((TopCat.toSSet.obj X).ιChainComplex σ ⊗ₘ
      (TopCat.toSSet.obj Y).ιChainComplex τ) ≫ f =
      ((TopCat.toSSet.obj X).ιChainComplex σ ⊗ₘ
      (TopCat.toSSet.obj Y).ιChainComplex τ) ≫ g) : f = g := by
  let hc := isColimitCofanMkObjOfIsColimit
    (tensorRight (((chains R).obj Y).X q)) _ _
    ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (coeff R) p)
  let hd := isColimitCofanMkObjOfIsColimit (tensorLeft (coeff R)) _ _
    ((TopCat.toSSet.obj Y).isColimitChainComplexXCofan (coeff R) q)
  apply hc.hom_ext
  intro σ
  apply hd.hom_ext
  intro τ
  change (coeff R ◁ (TopCat.toSSet.obj Y).ιChainComplex τ.as) ≫
    ((TopCat.toSSet.obj X).ιChainComplex σ.as ▷ (((chains R).obj Y).X q)) ≫ f =
    (coeff R ◁ (TopCat.toSSet.obj Y).ιChainComplex τ.as) ≫
    ((TopCat.toSSet.obj X).ιChainComplex σ.as ▷ (((chains R).obj Y).X q)) ≫ g
  have hh := h σ.as τ.as
  rw [tensorHom_def', Category.assoc, Category.assoc] at hh
  exact hh

abbrev model (p q : ℕ) : TopCat.{u} × TopCat.{u} :=
  (SimplexCategory.toTop.obj ⦋p⦌, SimplexCategory.toTop.obj ⦋q⦌)

/-- Pair of singular generators in their total degree. -/
def generator (X : TopCat.{u} × TopCat.{u}) (p q n : ℕ) (h : p + q = n)
    (σ : (TopCat.toSSet.obj X.1).obj (.op ⦋p⦌))
    (τ : (TopCat.toSSet.obj X.2).obj (.op ⦋q⦌)) :
    coeff R ⊗ coeff R ⟶ ((tensorChains R).obj X).X n :=
  ((TopCat.toSSet.obj X.1).ιChainComplex σ ⊗ₘ
    (TopCat.toSSet.obj X.2).ιChainComplex τ) ≫
      HomologicalComplex.ιTensorObj ((chains R).obj X.1) ((chains R).obj X.2) p q n h

@[reassoc]
lemma generator_naturality (X Y : TopCat.{u} × TopCat.{u}) (f : X ⟶ Y)
    (p q n : ℕ) (h : p + q = n)
    (σ : (TopCat.toSSet.obj X.1).obj (.op ⦋p⦌))
    (τ : (TopCat.toSSet.obj X.2).obj (.op ⦋q⦌)) :
    generator R X p q n h σ τ ≫ ((tensorChains R).map f).f n =
      generator R Y p q n h ((TopCat.toSSet.map f.1).app _ σ)
        ((TopCat.toSSet.map f.2).app _ τ) := by
  change generator R X p q n h σ τ ≫
    (HomologicalComplex.tensorHom ((chains R).map f.1) ((chains R).map f.2)).f n = _
  dsimp only [generator]
  rw [Category.assoc, SingularProductTensor.ι_tensor_map]
  erw [tensorHom_comp_tensorHom_assoc]
  erw [SSet.ι_chainComplexMap_f, SSet.ι_chainComplexMap_f]

lemma generator_hom_ext (X : TopCat.{u} × TopCat.{u}) (n : ℕ)
    {V : ModuleCat.{u} R} {f g : ((tensorChains R).obj X).X n ⟶ V}
    (h : ∀ p q (hpq : p + q = n) σ τ,
      generator R X p q n hpq σ τ ≫ f = generator R X p q n hpq σ τ ≫ g) :
    f = g := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  apply pair_hom_ext R X.1 X.2 p q
  intro σ τ
  exact (Category.assoc _ _ _).symm.trans ((h p q hpq σ τ).trans (Category.assoc _ _ _))

/-- Extend model values over every tensor bidegree by the native total coproduct. -/
@[irreducible]
def extendApp (n : ℕ) (V : TopCat.{u} × TopCat.{u} ⥤ ModuleCat.{u} R)
    (v : ∀ p q, p + q = n → (coeff R ⊗ coeff R ⟶ V.obj (model p q)))
    (X : TopCat.{u} × TopCat.{u}) : ((tensorChains R).obj X).X n ⟶ V.obj X :=
  HomologicalComplex.mapBifunctorDesc (fun p q h ↦ extendPair R X.1 X.2 p q _
    (fun σ τ ↦ v p q h ≫ V.map (σ.down, τ.down)))

@[reassoc (attr := simp)]
lemma generator_extendApp (n : ℕ) (V : TopCat.{u} × TopCat.{u} ⥤ ModuleCat.{u} R)
    (v : ∀ p q, p + q = n → (coeff R ⊗ coeff R ⟶ V.obj (model p q)))
    (X : TopCat.{u} × TopCat.{u}) (p q : ℕ) (h : p + q = n) σ τ :
    generator R X p q n h σ τ ≫ extendApp R n V v X =
      v p q h ≫ V.map (σ.down, τ.down) := by
  unfold extendApp
  dsimp only [generator]
  rw [Category.assoc]
  erw [HomologicalComplex.ι_mapBifunctorDesc]
  exact pair_extendPair R X.1 X.2 p q _ _ σ τ

/-- The tensor generator extension is natural. -/
def extend (n : ℕ) (V : TopCat.{u} × TopCat.{u} ⥤ ModuleCat.{u} R)
    (v : ∀ p q, p + q = n → (coeff R ⊗ coeff R ⟶ V.obj (model p q))) :
    (chainComplexOfFunctor (tensorChains R)).X n ⟶ V where
  app := extendApp R n V v
  naturality X Y f := by
    apply generator_hom_ext R X n
    intro p q h σ τ
    change _ ≫ ((tensorChains R).map f).f n ≫ extendApp R n V v Y =
      _ ≫ extendApp R n V v X ≫ V.map f
    erw [← Category.assoc, generator_naturality, generator_extendApp]
    erw [← Category.assoc, generator_extendApp, Category.assoc, ← V.map_comp]
    rfl

/-- Evaluation at the identity simplex pair recovers any natural transformation. -/
theorem extend_evaluate (n : ℕ) (V : TopCat.{u} × TopCat.{u} ⥤ ModuleCat.{u} R)
    (r : (chainComplexOfFunctor (tensorChains R)).X n ⟶ V) :
    extend R n V (fun p q h ↦ generator R (model p q) p q n h
      (ULift.up (𝟙 _)) (ULift.up (𝟙 _)) ≫ r.app (model p q)) = r := by
  apply NatTrans.ext
  funext X
  apply generator_hom_ext R X n
  intro p q h σ τ
  change _ ≫ extendApp R n V _ X = _
  erw [generator_extendApp]
  erw [Category.assoc, ← r.naturality]
  dsimp only [chainComplexOfFunctor, Functor.comp_map, HomologicalComplex.eval]
  erw [← Category.assoc, generator_naturality]
  have hσ : (TopCat.toSSet.map σ.down).app _ (ULift.up (𝟙 _)) = σ := by
    rfl
  have hτ : (TopCat.toSSet.map τ.down).app _ (ULift.up (𝟙 _)) = τ := by
    rfl
  erw [hσ, hτ]

/-- Natural postcomposition commutes with the free extension. -/
theorem extend_comp (n : ℕ) (V W : TopCat.{u} × TopCat.{u} ⥤ ModuleCat.{u} R)
    (v : ∀ p q, p + q = n → (coeff R ⊗ coeff R ⟶ V.obj (model p q)))
    (f : V ⟶ W) :
    extend R n V v ≫ f = extend R n W (fun p q h ↦ v p q h ≫ f.app (model p q)) := by
  apply NatTrans.ext
  funext X
  apply generator_hom_ext R X n
  intro p q h σ τ
  change _ ≫ extendApp R n V v X ≫ f.app X = _ ≫ extendApp R n W _ X
  erw [← Category.assoc, generator_extendApp, generator_extendApp]
  erw [Category.assoc, f.naturality, Category.assoc]

/-- Fillings at every identity simplex pair extend naturally to the whole tensor degree. -/
theorem lift_natural (n : ℕ) (V W : TopCat.{u} × TopCat.{u} ⥤ ModuleCat.{u} R)
    (d : V ⟶ W) (r : (chainComplexOfFunctor (tensorChains R)).X n ⟶ W)
    (h : ∀ p q (hpq : p + q = n), ∃ v : coeff R ⊗ coeff R ⟶ V.obj (model p q),
      v ≫ d.app (model p q) = generator R (model p q) p q n hpq
        (ULift.up (𝟙 _)) (ULift.up (𝟙 _)) ≫ r.app (model p q)) :
    ∃ s : (chainComplexOfFunctor (tensorChains R)).X n ⟶ V, s ≫ d = r := by
  choose v hv using h
  refine ⟨extend R n V v, ?_⟩
  rw [extend_comp]
  simp only [hv]
  exact extend_evaluate R n W r

/-- Positive singular cycles on a product of lifted simplex models bound.
The product of lifts is canonically the lift of the convex product; transport
Bredon's cone contraction across that homeomorphism. -/
theorem product_model_fill (p q n : ℕ) {V : ModuleCat.{u} R}
    (v : V ⟶ ((productChains R).obj (model p q)).X (n + 1))
    (hv : v ≫ ((productChains R).obj (model p q)).d (n + 1) n = 0) :
    ∃ w : V ⟶ ((productChains R).obj (model p q)).X (n + 2),
      w ≫ ((productChains R).obj (model p q)).d (n + 2) (n + 1) = v := by
  let e : (model.{u} p q).1 ⊗ (model p q).2 ≅
      LiftedSingularCone.space (.product p q) :=
    { hom := TopCat.ofHom ⟨fun x ↦ ULift.up (x.1.down, x.2.down),
        continuous_uliftUp.comp ((continuous_uliftDown.comp continuous_fst).prodMk
          (continuous_uliftDown.comp continuous_snd))⟩
      inv := TopCat.ofHom ⟨fun x ↦ (ULift.up x.down.1, ULift.up x.down.2),
        (continuous_uliftUp.comp (continuous_fst.comp continuous_uliftDown)).prodMk
          (continuous_uliftUp.comp (continuous_snd.comp continuous_uliftDown))⟩ }
  let E : (productChains R).obj (model p q) ≅
      LiftedSingularCone.chains R (.product p q) := (chains R).mapIso e
  let o : LiftedSingularCone.space.{u} (.product p q) :=
    ULift.up ((SingularProductTensor.modelPoint.{u} p).down,
      (SingularProductTensor.modelPoint.{u} q).down)
  let H := LiftedSingularCone.contraction R (.product p q) o
  let z : V ⟶ (LiftedSingularCone.chains R (.product p q)).X (n + 1) :=
    v ≫ E.hom.f (n + 1)
  have hz : z ≫ (LiftedSingularCone.chains R (.product p q)).d (n + 1) n = 0 := by
    dsimp only [z]
    rw [Category.assoc, E.hom.comm, ← Category.assoc, hv, zero_comp]
  have hH := H.comm (n + 1)
  rw [HomologicalComplex.id_f, Homotopy.dNext_succ_chainComplex,
    Homotopy.prevD_chainComplex] at hH
  have heps : (LiftedSingularCone.epsilon R (.product p q) o).f (n + 1) = 0 := rfl
  rw [heps, add_zero] at hH
  have hh : (z ≫ H.hom (n + 1) (n + 2)) ≫
      (LiftedSingularCone.chains R (.product p q)).d (n + 2) (n + 1) = z := by
    have hh := congrArg (fun f ↦ z ≫ f) hH
    simpa only [Category.comp_id, Preadditive.comp_add, ← Category.assoc,
      hz, zero_comp, zero_add] using hh.symm
  refine ⟨z ≫ H.hom (n + 1) (n + 2) ≫ E.inv.f (n + 2), ?_⟩
  simp only [Category.assoc]
  rw [E.inv.comm]
  simp only [← Category.assoc]
  rw [hh]
  dsimp only [z]
  rw [Category.assoc]
  have he := congrArg (fun f ↦ f.f (n + 1)) E.hom_inv_id
  dsimp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at he
  rw [he, Category.comp_id]

/-- Natural positive-cycle filling for a tensor degree, by free model extension. -/
theorem fill_positive (k n : ℕ)
    (r : (chainComplexOfFunctor (tensorChains R)).X k ⟶
      (chainComplexOfFunctor (productChains R)).X (n + 1))
    (hr : r ≫ (chainComplexOfFunctor (productChains R)).d (n + 1) n = 0) :
    ∃ s : (chainComplexOfFunctor (tensorChains R)).X k ⟶
      (chainComplexOfFunctor (productChains R)).X (n + 2),
      s ≫ (chainComplexOfFunctor (productChains R)).d (n + 2) (n + 1) = r := by
  refine lift_natural R k _ _
    ((chainComplexOfFunctor (productChains R)).d (n + 2) (n + 1)) r ?_
  intro p q hpq
  let v := generator R (model p q) p q k hpq (ULift.up (𝟙 _)) (ULift.up (𝟙 _)) ≫
    r.app (model p q)
  have hv : v ≫ ((productChains R).obj (model p q)).d (n + 1) n = 0 := by
    have h := NatTrans.congr_app hr (model p q)
    dsimp only [NatTrans.comp_app, zero_app, chainComplexOfFunctor] at h
    dsimp only [v]
    erw [Category.assoc, h, comp_zero]
  exact product_model_fill R p q n v hv

/-- The unique zero simplex of the singleton. -/
def pointSimplex : (TopCat.toSSet.obj point.{u}).obj (.op ⦋0⦌) :=
  (TopCat.toSSetObjEquiv _ _).symm (ContinuousMap.const _ PUnit.unit)

/-- The point inclusion selected by a zero simplex. -/
def pointMap (X : TopCat.{u}) (σ : (TopCat.toSSet.obj X).obj (.op ⦋0⦌)) : point ⟶ X :=
  TopCat.ofHom (ContinuousMap.const _
    ((σ.down : SimplexCategory.toTop.obj ⦋0⦌ ⟶ X).hom (default : SimplexCategory.toTop.obj ⦋0⦌)))

lemma map_pointSimplex (X : TopCat.{u}) (σ : (TopCat.toSSet.obj X).obj (.op ⦋0⦌)) :
    (TopCat.toSSet.map (pointMap X σ)).app _ pointSimplex = σ := by
  apply ULift.ext
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro t
  change (σ.down : SimplexCategory.toTop.obj ⦋0⦌ ⟶ X).hom
    (default : SimplexCategory.toTop.obj ⦋0⦌) =
      (σ.down : SimplexCategory.toTop.obj ⦋0⦌ ⟶ X).hom t
  congr 1
  exact Subsingleton.elim (α := SimplexCategory.toTop.obj ⦋0⦌) _ _

/-- Equality at the point-pair generator determines a natural map in degree zero. -/
theorem zero_eq_of_point (V : TopCat.{u} × TopCat.{u} ⥤ ModuleCat.{u} R)
    (f g : (chainComplexOfFunctor (tensorChains R)).X 0 ⟶ V)
    (h : generator R pointPair 0 0 0 rfl pointSimplex pointSimplex ≫ f.app pointPair =
      generator R pointPair 0 0 0 rfl pointSimplex pointSimplex ≫ g.app pointPair) : f = g := by
  apply NatTrans.ext
  funext X
  apply generator_hom_ext R X 0
  intro p q hpq σ τ
  have hp : p = 0 := by omega
  have hq : q = 0 := by omega
  subst p
  subst q
  let m : pointPair ⟶ X := (pointMap X.1 σ, pointMap X.2 τ)
  have transport (r : (chainComplexOfFunctor (tensorChains R)).X 0 ⟶ V) :
      generator R pointPair 0 0 0 rfl pointSimplex pointSimplex ≫
          r.app pointPair ≫ V.map m = generator R X 0 0 0 hpq σ τ ≫ r.app X := by
    erw [← r.naturality]
    dsimp only [chainComplexOfFunctor, Functor.comp_map, HomologicalComplex.eval]
    erw [← Category.assoc, generator_naturality]
    dsimp only [m]
    erw [map_pointSimplex, map_pointSimplex]
  rw [← transport f, ← transport g]
  rw [← Category.assoc, ← Category.assoc, h]

end HolomorphicAnosov.SingularTensorGenerator

namespace HolomorphicAnosov.Topology

/-- Natural positive residuals from tensor singular chains to product singular
chains admit natural fillings. Source: Barr, Chapter 1 §6 Lemma 6.2, p.20,
and Chapter 5 §5 Proposition 5.5, p.116; Bredon, VI Theorem 1.3, pp.317–318.
Evaluate the residual on each identity simplex pair. The product cone fills
its positive cycle. Transport that filling along each pair of simplex maps;
tensor preservation of the two singular coproducts and the total coproduct
extend the values linearly. Evaluation recovers the residual, and natural
postcomposition commutes with extension, proving the boundary equation.
The construction works directly over ULift ℚ, including empty source spaces. -/
theorem singular_acyclic_models_BA_free_generator_residual_filling :
    let R := ULift.{u} ℚ
    let coefficient : ModuleCat.{u} R := ModuleCat.of R R
    let C : TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
      (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} R)).obj coefficient
    let A : TopCat.{u} × TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
      tensor TopCat.{u} ⋙ C
    let B : TopCat.{u} × TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
      (C.prod C) ⋙ tensor (ChainComplex (ModuleCat.{u} R) ℕ)
    ∀ (n : ℕ)
      (r : (chainComplexOfFunctor B).X (n + 1) ⟶
        (chainComplexOfFunctor A).X (n + 1)),
      r ≫ (chainComplexOfFunctor A).d (n + 1) n = 0 →
      ∃ s : (chainComplexOfFunctor B).X (n + 1) ⟶
        (chainComplexOfFunctor A).X (n + 2),
        s ≫ (chainComplexOfFunctor A).d (n + 2) (n + 1) = r := by
  exact fun n r hr ↦ SingularTensorGenerator.fill_positive (ULift.{u} ℚ) (n + 1) n r hr


end HolomorphicAnosov.Topology

