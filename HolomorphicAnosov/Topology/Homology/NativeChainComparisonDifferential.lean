import HolomorphicAnosov.Topology.Homology.RationalScalarTransport

/-!
# Differential compatibility of the native rational chain comparison

Source: Bredon, *Topology and Geometry*, VI §1, pp.316–318, for coefficient
extension of chain maps; pinned Mathlib `HomologicalComplex.Hom.comm` supplies
the exact native comparison equations, including off-shape components.
-/

open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u
namespace HolomorphicAnosov.RationalScalarTransport

/-- The native scalar comparison commutes with every singular-chain
 differential component.

Source: Bredon, *Topology and Geometry*, VI §1, pp.316–318, the coefficient
extension step; realized by the pinned Mathlib chain-complex comparison. The
statement is the concrete underlying-function form of
`HomologicalComplex.Hom.comm` for `nativeChainComparison`. It is the smallest
transport lemma needed before applying the signed rational shuffle boundary
identity to the lifted-rational carrier. It includes all zero and off-shape
cases because the chain-complex morphism equation does. -/
theorem nativeChainComparison_hom_differential
    (X : SSet.{u}) (i j : ℕ) (z : (transportedChains X).X i) :
    (X.chainComplex liftedCoefficients).d i j
        ((nativeChainComparison X).hom.f i z) =
      (nativeChainComparison X).hom.f j
        ((transportedChains X).d i j z) := by
  exact ConcreteCategory.congr_hom ((nativeChainComparison X).hom.comm i j) z

/-- The inverse comparison commutes with differential components as well.

Source: Bredon VI §1, pp.316–318, and Mathlib `HomologicalComplex.Hom.comm`.
Proof: evaluate the inverse chain morphism's commutation equation on `z` using
`ConcreteCategory.congr_hom`; the equation holds at every pair of degrees. -/
theorem nativeChainComparison_inv_differential
    (X : SSet.{u}) (i j : ℕ)
    (z : (X.chainComplex liftedCoefficients).X i) :
    (transportedChains X).d i j
        ((nativeChainComparison X).inv.f i z) =
      (nativeChainComparison X).inv.f j
        ((X.chainComplex liftedCoefficients).d i j z) := by
  exact ConcreteCategory.congr_hom ((nativeChainComparison X).inv.comm i j) z

end HolomorphicAnosov.RationalScalarTransport
