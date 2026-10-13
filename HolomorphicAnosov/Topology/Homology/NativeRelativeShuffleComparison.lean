import HolomorphicAnosov.Topology.SingularEilenbergZilberAcyclicModels
import HolomorphicAnosov.Topology.Homology.ModTwoSingularSupportHomology

/-!
# The signed shuffle on native one-relative-factor complexes

Source: Bredon, Topology and Geometry, VI Corollary 1.4 and the relative
Künneth paragraph, pp.318–320. The Eilenberg–Zilber cokernel is identified
with the actual singular pair complex using the product-subspace homeomorphism.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
universe u
namespace HolomorphicAnosov.NativeRelativeShuffleComparison
open SingularEilenbergZilber RationalScalarTransport

abbrev nativePair (X : TopCat.{u}) (B : Set X) :=
  Topology.Homology.singularSubspacePair X B

abbrev relativeComplex (X : TopCat.{u}) (B : Set X) :=
  (nativePair X B).chainComplex (ModuleCat.of LiftQ.{u} LiftQ.{u})

abbrev productSupport (X Y : TopCat.{u}) (B : Set X) : Set (X × Y) :=
  {w | w.1 ∈ B}

/-- The native singular-pair complex is the cokernel of the original subspace
chain inclusion. This is the comparison of the two categorical cokernel choices. -/
def subspaceCokernelIso (X : TopCat.{u}) (B : Set X) :
    cokernel (chainFunctor.map (subspaceInclusion X B)) ≅ relativeComplex X B :=
  CokernelCofork.mapIsoOfIsColimit (cokernelIsCokernel _)
    ((nativePair X B).isColimitCokernelCoforkChainComplex _)
    (Iso.refl _)

@[reassoc]
theorem subspaceCokernelIso_projection (X : TopCat.{u}) (B : Set X) :
    cokernel.π (chainFunctor.map (subspaceInclusion X B)) ≫
      (subspaceCokernelIso X B).hom =
      (nativePair X B).chainComplexπ (ModuleCat.of LiftQ.{u} LiftQ.{u}) := by
  exact (CokernelCofork.π_mapOfIsColimit (cokernelIsCokernel _)
    ((nativePair X B).cokernelCoforkChainComplex _) (𝟙 _)).trans (Category.id_comp _)

/-- The product of a subspace with Y is homeomorphic to its literal product
subspace in X×Y, with the same inclusion in the ambient product. -/
def productSupportHomeomorph (X Y : TopCat.{u}) (B : Set X) :
    B × Y ≃ₜ productSupport X Y B where
  toFun w := ⟨(w.1.val, w.2), w.1.property⟩
  invFun w := (⟨w.val.1, w.property⟩, w.val.2)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk _
  continuous_invFun :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val)

/-- Identify the Eilenberg–Zilber product cokernel with the native pair complex.
The domain comparison is induced by the preceding homeomorphism, while the
ambient product chain map is the identity. -/
def productCokernelIso (X Y : TopCat.{u}) (B : Set X) :
    cokernel (SingularEilenbergZilber.productFunctor.{u}.map ((subspaceInclusion X B, 𝟙 Y) : (TopCat.of B, Y) ⟶ (X, Y))) ≅
      relativeComplex (TopCat.of (X × Y)) (productSupport X Y B) := by
  let e : TopCat.of (B × Y) ≅ TopCat.of (productSupport X Y B) :=
    TopCat.isoOfHomeo (productSupportHomeomorph X Y B)
  let P := nativePair (TopCat.of (X × Y)) (productSupport X Y B)
  apply CokernelCofork.mapIsoOfIsColimit (cokernelIsCokernel _)
    (P.isColimitCokernelCoforkChainComplex _)
  refine Arrow.isoMk (chainFunctor.mapIso e) (Iso.refl _) ?_
  symm
  change chainFunctor.map ((tensor TopCat).map ((subspaceInclusion X B, 𝟙 Y) : (TopCat.of B, Y) ⟶ (X, Y))) ≫ 𝟙 _ =
    chainFunctor.map e.hom ≫
      chainFunctor.map (subspaceInclusion (TopCat.of (X × Y)) (productSupport X Y B))
  rw [Category.comp_id, ← Functor.map_comp]
  rfl

@[reassoc]
theorem productCokernelIso_projection (X Y : TopCat.{u}) (B : Set X) :
    cokernel.π (SingularEilenbergZilber.productFunctor.{u}.map ((subspaceInclusion X B, 𝟙 Y) : (TopCat.of B, Y) ⟶ (X, Y))) ≫
      (productCokernelIso X Y B).hom =
      (nativePair (TopCat.of (X × Y)) (productSupport X Y B)).chainComplexπ
        (ModuleCat.of LiftQ.{u} LiftQ.{u}) := by
  exact (CokernelCofork.π_mapOfIsColimit (cokernelIsCokernel _) _ _).trans
    (Category.id_comp _)

/-- The prescribed shuffle gives a homotopy equivalence from the tensor of the
native relative complex with the second absolute complex to the native relative
product complex. The projection equation pins its forward map to the original
shuffle, rather than choosing an unrelated homotopy equivalence.

Source: Bredon VI Corollary 1.4 and the one-relative-factor proof following
Theorem 1.6, pp.318–320. Descend the natural shuffle inverse homotopies through
both subspace cokernels. Tensoring commutes with the source cokernel. Identify
the target cokernel using the homeomorphism B×Y ≃ {(x,y) | x∈B}. Conjugate the
cokernel homotopy equivalence by these two isomorphisms. Their projection
identities preserve the displayed equality with the actual signed shuffle.
The construction works for any B, including empty and full subspaces.
DAG node: `topo.native_relative_shuffle_comparison_g1`. -/
theorem native_relative_shuffle_homotopy_equiv (X Y : TopCat.{u}) (B : Set X) :
    ∃ e : HomotopyEquiv
        (HomologicalComplex.tensorObj (relativeComplex X B) (chainFunctor.obj Y))
        (relativeComplex (TopCat.of (X × Y)) (productSupport X Y B)),
      HomologicalComplex.tensorHom
          ((nativePair X B).chainComplexπ (ModuleCat.of LiftQ.{u} LiftQ.{u}))
          (𝟙 (chainFunctor.obj Y)) ≫ e.hom =
        shuffleChainMap X Y ≫
          (nativePair (TopCat.of (X × Y)) (productSupport X Y B)).chainComplexπ
            (ModuleCat.of LiftQ.{u} LiftQ.{u}) := by
  obtain ⟨θ, HT, HA, _, _, _, _, _, _, _, _, hrel⟩ :=
    singular_eilenberg_zilber_acyclic_models.{u}
  obtain ⟨shR, θR, HTR, HAR, hsh, _, _, _, e, he⟩ := hrel X Y B
  let E := e ≪≫ (tensorRight (chainFunctor.obj Y)).mapIso (subspaceCokernelIso X B)
  let F := productCokernelIso X Y B
  have hE : cokernel.π (SingularEilenbergZilber.tensorFunctor.map
        ((subspaceInclusion X B, 𝟙 Y) : (TopCat.of B, Y) ⟶ (X, Y))) ≫ E.hom =
      HomologicalComplex.tensorHom
        ((nativePair X B).chainComplexπ (ModuleCat.of LiftQ.{u} LiftQ.{u}))
        (𝟙 (chainFunctor.obj Y)) := by
    change _ ≫ (e.hom ≫ _) = _
    rw [← Category.assoc, he]
    change (tensorRight (chainFunctor.obj Y)).map
        (cokernel.π (chainFunctor.map (subspaceInclusion X B))) ≫
      (tensorRight (chainFunctor.obj Y)).map (subspaceCokernelIso X B).hom =
      (tensorRight (chainFunctor.obj Y)).map
        ((nativePair X B).chainComplexπ (ModuleCat.of LiftQ.{u} LiftQ.{u}))
    rw [← Functor.map_comp, subspaceCokernelIso_projection]
  let H : HomotopyEquiv _ _ := ⟨shR, θR, HTR, HAR⟩
  let K := (HomotopyEquiv.ofIso E.symm).trans (H.trans (HomotopyEquiv.ofIso F))
  refine ⟨K, ?_⟩
  rw [← hE]
  change (_ ≫ E.hom) ≫ E.inv ≫ shR ≫ F.hom = _
  rw [Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, hsh, Category.assoc]
  rw [productCokernelIso_projection]
  rfl

/-- The native relative signed shuffle induces a bijection in every homology
degree, preserving its original chain projection formula. Source: Bredon VI
Corollary 1.4 and the relative paragraph p.320. Apply homology to the preceding
homotopy equivalence; inverse homotopies give inverse homology maps. -/
theorem native_relative_shuffle_homology_bijective (X Y : TopCat.{u}) (B : Set X) :
    ∃ f : HomologicalComplex.tensorObj (relativeComplex X B) (chainFunctor.obj Y) ⟶
        relativeComplex (TopCat.of (X × Y)) (productSupport X Y B),
      HomologicalComplex.tensorHom
          ((nativePair X B).chainComplexπ (ModuleCat.of LiftQ.{u} LiftQ.{u}))
          (𝟙 (chainFunctor.obj Y)) ≫ f =
        shuffleChainMap X Y ≫
          (nativePair (TopCat.of (X × Y)) (productSupport X Y B)).chainComplexπ
            (ModuleCat.of LiftQ.{u} LiftQ.{u}) ∧
      ∀ n : ℕ, Function.Bijective (HomologicalComplex.homologyMap f n).hom := by
  obtain ⟨e, he⟩ := native_relative_shuffle_homotopy_equiv X Y B
  exact ⟨e.hom, he, fun n ↦ ConcreteCategory.bijective_of_isIso _⟩

end HolomorphicAnosov.NativeRelativeShuffleComparison


