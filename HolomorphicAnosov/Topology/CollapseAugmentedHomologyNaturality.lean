import HolomorphicAnosov.Topology.AugmentedCollapseProjectionNaturality
import HolomorphicAnosov.Topology.AugmentedRelativeHomologyIso
import HolomorphicAnosov.Topology.ZeroAugmentHomologyIsoNaturality

/-! Source: Hatcher, *Algebraic Topology*, p.118 (augmented relative chains)
and p.124 (collapse naturality). DAG node: `topo.collapse_augmented_homology_naturality`. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace HolomorphicAnosov.GoodPair
universe u
/-- Naturality of the collapse map with the augmentation comparison.
Source: Hatcher pp.118,124. Apply homology to the augmented projection square,
postcompose by the quotient grading comparison, and use naturality of the
zero-augmentation comparison on the native relative chain map. Associativity
identifies the resulting composite with the stated literal collapse map. -/
theorem collapse_augmented_homology_naturality (X : TopCat.{u}) (A : Set X) (n : ℕ) :
    integralReducedSingularHomologyMap (collapseMorphism X A) n ≫
        HomologicalComplex.homologyMap
          (augmentedRelativeProjection (TopCat.of (Collapsed A)) (collapsedPart A)) (n + 1) ≫
        (augmentedRelativeHomologyIso (TopCat.of (Collapsed A)) (collapsedPart A) n).hom =
      HomologicalComplex.homologyMap (augmentedRelativeProjection X A) (n + 1) ≫
        (augmentedRelativeHomologyIso X A n).hom ≫
          SSetPair.homologyMap (collapseSingularPairMap X A)
            reducedSingularIntegralCoefficients n := by
  let F : augmentedRelativeChains X A ⟶
      augmentedRelativeChains (TopCat.of (Collapsed A)) (collapsedPart A) :=
    augmentedRelativeChainsMap (collapseSingularPairMap X A)
  have hp : HomologicalComplex.homologyMap
      (augmentedIntegralSingularChainsMap (collapseMorphism X A)) (n + 1) ≫
      HomologicalComplex.homologyMap
        (augmentedRelativeProjection (TopCat.of (Collapsed A)) (collapsedPart A)) (n + 1) =
      HomologicalComplex.homologyMap (augmentedRelativeProjection X A) (n + 1) ≫
        HomologicalComplex.homologyMap F (n + 1) := by
    exact (HomologicalComplex.homologyMap_comp _ _ _).symm.trans
      ((congrArg (fun f ↦ HomologicalComplex.homologyMap f (n + 1))
        (collapseAugmentedProjection_naturality_g12 X A)).trans
          (HomologicalComplex.homologyMap_comp _ F _))
  have hs := zeroAugmentHomologyIso_naturality
    (SSetPair.chainComplexMap (collapseSingularPairMap X A) reducedSingularIntegralCoefficients)
    F n rfl
  change HomologicalComplex.homologyMap
      (augmentedIntegralSingularChainsMap (collapseMorphism X A)) (n + 1) ≫ _ = _
  have hp' := congrArg (fun g ↦ g ≫
    (augmentedRelativeHomologyIso (TopCat.of (Collapsed A)) (collapsedPart A) n).hom) hp
  have hs' := congrArg (fun g ↦ HomologicalComplex.homologyMap
    (augmentedRelativeProjection X A) (n + 1) ≫ g) hs
  exact (Category.assoc _ _ _).symm.trans (hp'.trans ((Category.assoc _ _ _).trans hs'))


end HolomorphicAnosov.GoodPair

