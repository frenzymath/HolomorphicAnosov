import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
open CategoryTheory CategoryTheory.Limits Opposite
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain
set_option backward.isDefEq.respectTransparency false
/-- A degreewise finite product decomposition of cochain complexes induces the
corresponding product decomposition of the explicit cohomology quotients.
Source: Hatcher, *Algebraic Topology*, p.202; DAG
`algebra.cochain_finite_product_quotient_bijective_g13`.

The degreewise linear bijections make each evaluated fan a product. Evaluation
jointly detects limits of complexes. The homology functor is additive and hence
preserves finite products. Identify the resulting module product with the
function module, and conjugate each homology map by the canonical isomorphism
to its explicit cycles/boundaries quotient. -/
theorem cochain_finite_product_quotient_bijective (R : Type u) [CommRing R] {ι : Type u} [Fintype ι]
    (P : CochainComplex (ModuleCat.{u} R) ℕ)
    (Q : ι → CochainComplex (ModuleCat.{u} R) ℕ) (f : ∀ j, P ⟶ Q j)
    (hf : ∀ n, Function.Bijective (fun x : P.X n => fun j => (f j).f n x)) (n : ℕ) :
    Function.Bijective (fun x : quotient R P n => fun j => quotientMap R (f j) n x) := by
  have hp : IsLimit (Fan.mk P f) := by
    apply HomologicalComplex.isLimitOfEval
    intro k
    refine (isLimitMapConeFanMkEquiv (HomologicalComplex.eval _ _ k) Q f).symm ?_
    let L : P.X k →ₗ[R] ∀ j, (Q j).X k := LinearMap.pi (fun j => ((f j).f k).hom)
    let e := (LinearEquiv.ofBijective L (hf k)).toModuleIso
    apply IsLimit.ofIsoLimit (ModuleCat.productConeIsLimit (fun j => (Q j).X k))
    refine Fan.ext e.symm ?_
    intro j
    change ModuleCat.ofHom (LinearMap.proj j) = e.inv ≫ (f j).f k
    apply (cancel_epi e.hom).mp
    simp only [Iso.hom_inv_id_assoc]
    rfl
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n
  have hh := isLimitFanMkObjOfIsLimit H Q f hp
  let e := hh.conePointUniqueUpToIso
    (ModuleCat.productConeIsLimit (fun j => H.obj (Q j)))
  have he : Function.Bijective (fun x : H.obj P => fun j => H.map (f j) x) := by
    have eh : e.hom = ModuleCat.ofHom (LinearMap.pi (fun j => (H.map (f j)).hom)) := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      funext j
      exact congrArg (fun m => m x) (hh.conePointUniqueUpToIso_hom_comp
        (ModuleCat.productConeIsLimit (fun j => H.obj (Q j))) ⟨j⟩)
    have hb := (ConcreteCategory.isIso_iff_bijective e.hom).mp inferInstance
    rwa [eh] at hb
  let a := (P.sc n).moduleCatHomologyIso
  let b := fun j => ((Q j).sc n).moduleCatHomologyIso
  have ha : Function.Bijective a.inv := (ConcreteCategory.isIso_iff_bijective a.inv).mp inferInstance
  have hb : Function.Bijective (fun x : ∀ j, H.obj (Q j) => fun j => (b j).hom (x j)) := by
    constructor
    · intro x y h
      funext j
      exact ((ConcreteCategory.isIso_iff_bijective (b j).hom).mp inferInstance).injective
        (congrFun h j)
    · intro x
      refine ⟨fun j => (b j).inv (x j), ?_⟩
      funext j
      exact congrArg (fun m => m (x j)) (b j).inv_hom_id
  exact hb.comp (he.comp ha)
end HolomorphicAnosov.SingularCochain
