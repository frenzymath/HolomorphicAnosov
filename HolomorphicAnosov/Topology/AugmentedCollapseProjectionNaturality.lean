import HolomorphicAnosov.Topology.GoodPairCollapseSingularPairMap
import HolomorphicAnosov.Topology.AugmentedRelativeProjection
import HolomorphicAnosov.Topology.AugmentedRelativeChainsMap

/-!
# Naturality of the augmented relative projection for collapse

Source: Hatcher, *Algebraic Topology*, augmented pair sequence p.118 and
Proposition 2.22 p.124. The square uses the actual collapse quotient map,
its induced map of singular pairs, and the native relative chain projection.
DAG: `topo.good_pair_collapse_augmented_projection_naturality_g12`.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits Set
open scoped ZeroObject
namespace HolomorphicAnosov.GoodPair
universe u

/-- The literal quotient projection commutes with the augmented relative map.
Source: Hatcher pp.118,124. At augmented index zero both composites vanish.
At each successor index apply the native simplicial-pair relative projection
naturality square and take its component. No quotient-simplex lifting is used. -/
theorem collapseAugmentedProjection_naturality_g12 (X : TopCat.{u}) (A : Set X) :
    augmentedIntegralSingularChainsMap (collapseMorphism X A) ≫
        augmentedRelativeProjection (TopCat.of (Collapsed A)) (collapsedPart A) =
      augmentedRelativeProjection X A ≫
        augmentedRelativeChainsMap (collapseSingularPairMap X A) := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero => change 𝟙 _ ≫ 0 = 0; exact comp_zero
  | succ n =>
      change (SSet.chainComplexMap (TopCat.toSSet.map (collapseMorphism X A))
          reducedSingularIntegralCoefficients.{u}).f n ≫
        ((singularSubspacePair (TopCat.of (Collapsed A)) (collapsedPart A)).chainComplexπ
          reducedSingularIntegralCoefficients.{u}).f n =
        ((singularSubspacePair X A).chainComplexπ
          reducedSingularIntegralCoefficients.{u}).f n ≫
          (SSetPair.chainComplexMap (collapseSingularPairMap X A)
            reducedSingularIntegralCoefficients.{u}).f n
      exact congrArg (fun g ↦ g.f n)
        ((((SSetPair.chainComplexFunctorπ (ModuleCat.{u} ℤ)).app
          reducedSingularIntegralCoefficients.{u}).naturality (collapseSingularPairMap X A)))

end HolomorphicAnosov.GoodPair

