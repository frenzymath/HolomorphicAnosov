import HolomorphicAnosov.Topology.Homology.IntegralRelativeChainProduct
import HolomorphicAnosov.Topology.SignedSingularCrossProductNaturality
import HolomorphicAnosov.Topology.RelativeProductSubspaceMap
import HolomorphicAnosov.Topology.SingularHomologyExcision.PairProjectionNaturality

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace HolomorphicAnosov.Topology
open HolomorphicAnosov.SignedSingularCrossProduct
universe u

private theorem projection_map_apply {X Y : TopCat.{u}} (f : X ⟶ Y)
    (A : Set X) (B : Set Y) (hf : Set.MapsTo f A B) (n : ℕ) (a : Chain X n) :
    (SSetPair.chainComplexMap (singularSubspacePairMap f A B hf)
      singularIntegralCoefficients).f n (relativeProjection X A n a) =
        relativeProjection Y B n (chainMap f n a) := by
  exact congrArg (fun k => k.hom a)
    (pair_projection_naturality (singularSubspacePairMap f A B hf)
      singularIntegralCoefficients n)

set_option backward.isDefEq.respectTransparency false in
/-- The native integral relative chain product is natural in maps of pairs. -/
theorem integralRelativeChainProduct_naturality
    (X Y X' Y' : TopCat.{u}) (f : X ⟶ X') (g : Y ⟶ Y')
    (A : Set X) (B : Set Y) (A' : Set X') (B' : Set Y')
    (hf : Set.MapsTo f A A') (hg : Set.MapsTo g B B') (p q : ℕ)
    (a : (RelativeComplex X A).X p) (b : (RelativeComplex Y B).X q) :
    (SSetPair.chainComplexMap (singularSubspacePairMap (productMap f g)
      (ProductSubspace A B) (ProductSubspace A' B')
      (relativeProductSubspace_map f g A B A' B' hf hg)) singularIntegralCoefficients).f (p+q)
        (integralRelativeChainProduct X Y A B p q a b) =
    integralRelativeChainProduct X' Y' A' B' p q
      ((SSetPair.chainComplexMap (singularSubspacePairMap f A A' hf)
        singularIntegralCoefficients).f p a)
      ((SSetPair.chainComplexMap (singularSubspacePairMap g B B' hg)
        singularIntegralCoefficients).f q b) := by
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (relativeProjection X A p)).mp
    (Cofork.IsColimit.epi ((singularSubspacePair X A).isColimitCokernelCoforkChainComplexX
      singularIntegralCoefficients p)) a
  obtain ⟨d, rfl⟩ := (ModuleCat.epi_iff_surjective (relativeProjection Y B q)).mp
    (Cofork.IsColimit.epi ((singularSubspacePair Y B).isColimitCokernelCoforkChainComplexX
      singularIntegralCoefficients q)) b
  rw [integralRelativeChainProduct_projection, projection_map_apply,
    projection_map_apply, projection_map_apply, integralRelativeChainProduct_projection]
  exact congrArg (relativeProjection (TopCat.of (X' × Y')) (ProductSubspace A' B') (p+q))
    (signedSingularCrossProduct_naturality X Y X' Y' f g p q c d)

end HolomorphicAnosov.Topology
