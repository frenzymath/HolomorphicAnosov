import HolomorphicAnosov.Topology.Homology.CompactSupportMayerVietorisData
import HolomorphicAnosov.Topology.Homology.IntegralULiftSupportChainComparison
import HolomorphicAnosov.Topology.Homology.IntegralSingularChainsULiftDegree
import HolomorphicAnosov.Topology.Homology.IntegralSingularChainsULiftBoundary
import HolomorphicAnosov.Topology.Homology.IntegralSSetPairULiftHomologyComparison

/-!
# Relative support homology transport across ULift
-/
noncomputable section
namespace HolomorphicAnosov
open HolomorphicAnosov.Topology _root_.Topology CategoryTheory
universe u

/-- Relative support homology with lifted integral coefficients is the ULift of the
native support homology after transporting the ambient and complement singular chains.

Source: Hatcher, Algebraic Topology, §2.1 pp.108–118 and coefficients p.153. The
landed degree and boundary comparisons identify the ambient and complement chain
complexes; the relative pair is their cokernel chain complex, so the comparison descends
through the pair quotient and then through homology. Empty supports and all degrees are
included. The explicit quotient-cocone descent is isolated as this named provider. -/
theorem integral_ulift_support_homology_transport
    (X : Type) [TopologicalSpace X] (A : Set X) (q : ℕ) :
    Nonempty (supportSingularHomology (TopCat.of (ULift.{u} X))
      {y : ULift.{u} X | y.down ∈ A}
      (ModuleCat.of ℤ (ULift.{u} ℤ)) q ≃ₗ[ℤ]
      ULift.{u} (supportSingularHomology (TopCat.of X) A
        (ModuleCat.of ℤ ℤ) q : Type 0)) := by
  let C := supportSingularChainComplex (TopCat.of X) A (ModuleCat.of ℤ ℤ)
  let F := ModuleCat.uliftFunctor.{u, 0} ℤ
  obtain ⟨e⟩ := integral_ulift_support_chain_comparison.{u} X A
  let h := HomologicalComplex.homologyMapIso e q ≪≫ (C.sc q).mapHomologyIso F
  exact ⟨h.toLinearEquiv.toAddEquiv.toIntLinearEquiv⟩

end HolomorphicAnosov
