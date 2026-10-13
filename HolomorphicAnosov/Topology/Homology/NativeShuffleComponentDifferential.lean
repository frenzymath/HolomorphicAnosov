import HolomorphicAnosov.Topology.Homology.RationalScalarTransportNaturality
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped Simplicial TensorProduct
noncomputable section
universe u
namespace HolomorphicAnosov.RationalScalarTransport
open HolomorphicAnosov.RationalScalarTransport
theorem nativeShuffleComponent_differential (X Y Z : SSet.{u}) (p q j : ℕ)
   
    (a : (X.chainComplex (ModuleCat.of LiftQ LiftQ)).X p)
   
    (b : (Y.chainComplex (ModuleCat.of LiftQ LiftQ)).X q)
   
    (sh : (X.chainComplex qCoefficients).X p ⊗[ℚ]
      (Y.chainComplex qCoefficients).X q →ₗ[ℚ]
      (Z.chainComplex qCoefficients).X (p+q)) :
    (Z.chainComplex (ModuleCat.of LiftQ LiftQ)).d (p+q) j
      (nativeShuffleComponent X Y Z p q sh (a ⊗ₜ[LiftQ] b)) =
    ((nativeChainComparison Z).hom.f j).hom
      ((((scalarFunctor.mapHomologicalComplex (.down ℕ)).obj (Z.chainComplex qCoefficients)).d (p+q) j)
        ((scalarFunctor.map (ModuleCat.ofHom sh)).hom
        ((tensorScalarComparison _ _).toLinearMap
          (TensorProduct.map ((nativeChainComparison X).inv.f p).hom
            ((nativeChainComparison Y).inv.f q).hom (a ⊗ₜ[LiftQ] b))))) := by
  rw [nativeShuffleComponent_tmul]
  let z := (scalarFunctor.map (ModuleCat.ofHom sh)).hom
      ((tensorScalarComparison _ _).toLinearMap
        (TensorProduct.map ((nativeChainComparison X).inv.f p).hom
          ((nativeChainComparison Y).inv.f q).hom (a ⊗ₜ[LiftQ] b)))
  have hc := (ConcreteCategory.congr_hom ((nativeChainComparison Z).hom.comm (p+q) j) z)
  change _ = _ at hc
  exact hc
end HolomorphicAnosov.RationalScalarTransport
