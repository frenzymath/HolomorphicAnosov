import HolomorphicAnosov.Topology.BarrNaturalHomotopyInduction
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Topology.Category.TopCat.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-! Free extension from the diagonal singular simplex, Bredon VI1.2–1.3,
pp.316–318. The source degree is freely represented by a pair of standard simplices. -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped Simplicial
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace HolomorphicAnosov.SingularProductGenerator

variable (R : Type u) [CommRing R]
abbrev coeff : ModuleCat.{u} R := ModuleCat.of R R
abbrev chains : TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
  (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} R)).obj (coeff R)
abbrev productChains := tensor TopCat.{u} ⋙ chains R
abbrev model (n : ℕ) : TopCat.{u} × TopCat.{u} :=
  (SimplexCategory.toTop.obj ⦋n⦌, SimplexCategory.toTop.obj ⦋n⦌)

/-- The pair of coordinate maps of a product simplex. -/
def generatorMap {X : TopCat.{u} × TopCat.{u}} {n : ℕ}
    (σ : (TopCat.toSSet.obj (X.1 ⊗ X.2)).obj (.op ⦋n⦌)) : model n ⟶ X :=
  (σ.down ≫ TopCat.ofHom ContinuousMap.fst, σ.down ≫ TopCat.ofHom ContinuousMap.snd)

/-- Linear extension of a value on the diagonal model generator. -/
def extendApp (n : ℕ) (V : TopCat.{u} × TopCat.{u} ⥤ ModuleCat.{u} R)
    (v : coeff R ⟶ V.obj (model n)) (X : TopCat.{u} × TopCat.{u}) :
    ((productChains R).obj X).X n ⟶ V.obj X :=
  ((TopCat.toSSet.obj (X.1 ⊗ X.2)).isColimitChainComplexXCofan (coeff R) n).desc
    (Cofan.mk _ (fun σ ↦ v ≫ V.map (generatorMap σ)))

@[reassoc (attr := simp)]
theorem ι_extendApp (n : ℕ) (V : TopCat.{u} × TopCat.{u} ⥤ ModuleCat.{u} R)
    (v : coeff R ⟶ V.obj (model n)) (X : TopCat.{u} × TopCat.{u})
    (σ : (TopCat.toSSet.obj (X.1 ⊗ X.2)).obj (.op ⦋n⦌)) :
    (TopCat.toSSet.obj (X.1 ⊗ X.2)).ιChainComplex σ ≫ extendApp R n V v X =
      v ≫ V.map (generatorMap σ) :=
  ((TopCat.toSSet.obj (X.1 ⊗ X.2)).isColimitChainComplexXCofan (coeff R) n).fac
    (Cofan.mk _ (fun σ ↦ v ≫ V.map (generatorMap σ))) (Discrete.mk σ)

/-- The diagonal-model extension is natural under arbitrary pairs of continuous maps. -/
def extend (n : ℕ) (V : TopCat.{u} × TopCat.{u} ⥤ ModuleCat.{u} R)
    (v : coeff R ⟶ V.obj (model n)) :
    (chainComplexOfFunctor (productChains R)).X n ⟶ V where
  app := extendApp R n V v
  naturality X Y f := by
    apply SSet.chainComplex_hom_ext
    intro σ
    change _ ≫ (SSet.chainComplexMap (TopCat.toSSet.map (f.1 ⊗ₘ f.2)) (coeff R)).f n ≫ _ = _
    simp only [← Category.assoc]
    erw [SSet.ι_chainComplexMap_f, ι_extendApp, ι_extendApp]
    erw [Category.assoc, ← V.map_comp]
    rfl

/-- The identity diagonal generator on its pair of standard simplices. -/
def diagonal (n : ℕ) :
    (TopCat.toSSet.obj ((model.{u} n).1 ⊗ (model.{u} n).2)).obj (.op ⦋n⦌) :=
  ULift.up (TopCat.ofHom ⟨fun t ↦ (t,t), continuous_id.prodMk continuous_id⟩)

/-- Evaluation of a natural map on the diagonal model generator determines it.
Source: Bredon VI1.2–1.3, pp.316–318. Every product simplex factors through
the diagonal by its two coordinate maps; naturality gives the displayed formula,
and the singular coproduct universal property extends it to all chains. -/
theorem extend_evaluate (n : ℕ) (V : TopCat.{u} × TopCat.{u} ⥤ ModuleCat.{u} R)
    (r : (chainComplexOfFunctor (productChains R)).X n ⟶ V) :
    extend R n V ((TopCat.toSSet.obj ((model n).1 ⊗ (model n).2)).ιChainComplex
      (diagonal n) ≫ r.app (model n)) = r := by
  apply NatTrans.ext
  funext X
  apply SSet.chainComplex_hom_ext
  intro σ
  change _ ≫ extendApp R n V _ X = _
  erw [ι_extendApp]
  erw [Category.assoc, ← r.naturality]
  erw [← Category.assoc]
  change _ ≫ (SSet.chainComplexMap (TopCat.toSSet.map
    ((generatorMap σ).1 ⊗ₘ (generatorMap σ).2)) (coeff R)).f n ≫ _ = _
  erw [← Category.assoc, SSet.ι_chainComplexMap_f]
  congr 2

/-- Extension commutes with postcomposition by a natural map. -/
theorem extend_comp (n : ℕ) (V W : TopCat.{u} × TopCat.{u} ⥤ ModuleCat.{u} R)
    (v : coeff R ⟶ V.obj (model n)) (f : V ⟶ W) :
    extend R n V v ≫ f = extend R n W (v ≫ f.app (model n)) := by
  apply NatTrans.ext
  funext X
  apply SSet.chainComplex_hom_ext
  intro σ
  change _ ≫ extendApp R n V v X ≫ f.app X = _ ≫ extendApp R n W _ X
  simp only [← Category.assoc]
  erw [ι_extendApp, ι_extendApp]
  erw [Category.assoc, f.naturality, Category.assoc]

/-- Modelwise fillers extend to natural fillers from each product singular degree.
Source: Bredon VI1.2–1.3, pp.316–318. Evaluate the residual at the diagonal
model generator, fill it on that model, and freely extend the filling. Extension
commutes with the differential, and the residual is recovered by evaluation. -/
theorem lift_natural (n : ℕ) (V W : TopCat.{u} × TopCat.{u} ⥤ ModuleCat.{u} R)
    (d : V ⟶ W) (r : (chainComplexOfFunctor (productChains R)).X n ⟶ W)
    (h : ∃ v : coeff R ⟶ V.obj (model n),
      v ≫ d.app (model n) =
        (TopCat.toSSet.obj ((model n).1 ⊗ (model n).2)).ιChainComplex (diagonal n) ≫
          r.app (model n)) :
    ∃ s : (chainComplexOfFunctor (productChains R)).X n ⟶ V, s ≫ d = r := by
  obtain ⟨v, hv⟩ := h
  exact ⟨extend R n V v, by rw [extend_comp, hv, extend_evaluate]⟩

abbrev point : TopCat.{u} := TopCat.of PUnit
abbrev pointPair : TopCat.{u} × TopCat.{u} := (point, point)

/-- The canonical generator on the one-point product. -/
def pointSimplex : (TopCat.toSSet.obj (point.{u} ⊗ point.{u})).obj (.op ⦋0⦌) :=
  (TopCat.toSSetObjEquiv _ _).symm (ContinuousMap.const _ (PUnit.unit, PUnit.unit))

/-- The pair of point inclusions determined by a zero simplex. -/
def pointMap (X : TopCat.{u} × TopCat.{u})
    (σ : (TopCat.toSSet.obj (X.1 ⊗ X.2)).obj (.op ⦋0⦌)) : pointPair ⟶ X :=
  (TopCat.ofHom (ContinuousMap.const _ ((σ.down : SimplexCategory.toTop.obj ⦋0⦌ ⟶ X.1 ⊗ X.2).hom (default : SimplexCategory.toTop.obj ⦋0⦌)).1),
    TopCat.ofHom (ContinuousMap.const _ ((σ.down : SimplexCategory.toTop.obj ⦋0⦌ ⟶ X.1 ⊗ X.2).hom (default : SimplexCategory.toTop.obj ⦋0⦌)).2))

lemma map_pointSimplex (X : TopCat.{u} × TopCat.{u})
    (σ : (TopCat.toSSet.obj (X.1 ⊗ X.2)).obj (.op ⦋0⦌)) :
    (TopCat.toSSet.map ((pointMap X σ).1 ⊗ₘ (pointMap X σ).2)).app _ pointSimplex = σ := by
  apply ULift.ext
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro t
  change (σ.down : SimplexCategory.toTop.obj ⦋0⦌ ⟶ X.1 ⊗ X.2).hom (default : SimplexCategory.toTop.obj ⦋0⦌) = (σ.down : SimplexCategory.toTop.obj ⦋0⦌ ⟶ X.1 ⊗ X.2).hom t
  congr 1
  exact Subsingleton.elim (α := SimplexCategory.toTop.obj ⦋0⦌) _ _

/-- Equality at the canonical point-pair generator forces degree-zero equality.
Source: Bredon VI1.2–1.3, pp.316–318. Every zero simplex is the pushforward
of that generator under its point inclusions. Naturality transports the given
equality to each generator; the coproduct universal property proves equality. -/
theorem zero_eq_of_point (V : TopCat.{u} × TopCat.{u} ⥤ ModuleCat.{u} R)
    (f g : (chainComplexOfFunctor (productChains R)).X 0 ⟶ V)
    (h : (TopCat.toSSet.obj (point ⊗ point)).ιChainComplex pointSimplex ≫
        f.app pointPair =
      (TopCat.toSSet.obj (point ⊗ point)).ιChainComplex pointSimplex ≫ g.app pointPair) :
    f = g := by
  apply NatTrans.ext
  funext X
  apply SSet.chainComplex_hom_ext
  intro σ
  have transport (r : (chainComplexOfFunctor (productChains R)).X 0 ⟶ V) :
      (TopCat.toSSet.obj (point ⊗ point)).ιChainComplex pointSimplex ≫
          r.app pointPair ≫ V.map (pointMap X σ) =
        (TopCat.toSSet.obj (X.1 ⊗ X.2)).ιChainComplex σ ≫ r.app X := by
    erw [← r.naturality]
    change _ ≫ (SSet.chainComplexMap (TopCat.toSSet.map
      ((pointMap X σ).1 ⊗ₘ (pointMap X σ).2)) (coeff R)).f 0 ≫ _ = _
    erw [← Category.assoc, SSet.ι_chainComplexMap_f, map_pointSimplex]
  erw [← transport f, ← transport g]
  erw [← Category.assoc, ← Category.assoc, h]

end HolomorphicAnosov.SingularProductGenerator
