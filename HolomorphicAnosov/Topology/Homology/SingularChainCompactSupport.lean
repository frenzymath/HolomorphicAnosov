import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex

/-!
# Compact image support of ordinary integral singular chains

Hatcher, *Algebraic Topology*, Proposition 2B.1(a), proof, printed p.170,
uses compactness of the union of the simplex images in a finite singular chain.
The chains here are the degree objects of Mathlib's ordinary, unnormalized
singular chain complex. The coproduct universal property gives their actual
finitely supported coefficients, rather than choosing a presentation.
-/

noncomputable section

namespace HolomorphicAnosov

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

/-- The ordinary integral singular `n`-chains of `X`, as in Hatcher, p.170.

This is Mathlib's unnormalized chain module on the actual singular simplicial
set. `ULift ℤ` changes only the universe of the coefficient module. -/
abbrev IntegralSingularChain (X : TopCat.{u}) (n : ℕ) :=
  ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ))).X n

/-- The canonical finite coefficients of an ordinary singular chain.

Source: Hatcher, p.170, and Mathlib's `SSet.isColimitChainComplexXCofan` and
`ModuleCat.finsuppCoconeIsColimit`. The isomorphism of these two coproducts
sends each singular-simplex summand to the same finitely supported generator;
it therefore retains the original integral coefficients, including cancellation. -/
def integralSingularChainCoefficients (X : TopCat.{u}) (n : ℕ) :
    IntegralSingularChain X n ≃ₗ[ℤ]
      ((TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌) →₀ ULift.{u} ℤ) :=
  ((TopCat.toSSet.obj X).isColimitChainComplexXCofan
      (ModuleCat.of ℤ (ULift.{u} ℤ)) n).coconePointUniqueUpToIso
    (ModuleCat.finsuppCoconeIsColimit ℤ (ULift.{u} ℤ)
      ((TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌))) |>.toLinearEquiv

/-- The union of images of the simplices with nonzero coefficients in a chain.

Source: Hatcher, Proposition 2B.1(a), proof, p.170. This is the literal image
union, without closure or any neighbourhood enlargement. Repeated generators
are consolidated in the native chain module before its finite support is taken. -/
def integralSingularChainImageSupport (X : TopCat.{u}) (n : ℕ)
    (c : IntegralSingularChain X n) : Set X :=
  ⋃ σ ∈ (integralSingularChainCoefficients X n c).support,
    Set.range (TopCat.toSSetObjEquiv X (Opposite.op ⦋n⦌) σ)

/-- Every ordinary finite integral singular chain has compact image support.

Source: Hatcher, *Algebraic Topology*, Proposition 2B.1(a), proof, p.170
(`literature/hatcher-at.txt:8500–8503`).

Proof: The degree-n chain object is the coproduct of one integral coefficient
module for every n-simplex of `TopCat.toSSet.obj X`. The canonical isomorphism
to the Finsupp coproduct sends each summand to the same generator. Its inverse
is supplied by the other coproduct universal property, and both composites
are identities by coproduct uniqueness. Hence the coefficient function of c
has finite support and is the actual consolidated singular-chain coefficient
function. Universe lifting of integers preserves zero and nonzero coefficients.
For every simplex in that support, `TopCat.toSSetObjEquiv` gives its continuous
map from `Convexity.StdSimplex ℝ (Fin (n + 1))` to the original space X.
The standard simplex is compact since its index type is finite. Each map's
range is therefore compact by `isCompact_range`. Apply
`Set.Finite.isCompact_biUnion` to the finite coefficient support and these
compact ranges. Its union is exactly `integralSingularChainImageSupport X n c`.
The zero chain has empty support and empty image union. The argument includes
degree zero, whose standard simplex is a point; if X is empty, all chains are
zero. It requires neither a separation axiom nor a nonempty ambient space.
If a finite presentation contains repetitions or zero coefficients, its
possibly larger listed-image union is compact by the same finite-union argument;
no equality with the consolidated support union is asserted. -/
theorem integralSingularChainImageSupport_isCompact (X : TopCat.{u}) (n : ℕ)
    (c : IntegralSingularChain X n) :
    IsCompact (integralSingularChainImageSupport X n c) := by
  apply (integralSingularChainCoefficients X n c).support.isCompact_biUnion
  intro σ hσ
  exact isCompact_range (TopCat.toSSetObjEquiv X (Opposite.op ⦋n⦌) σ).continuous

end HolomorphicAnosov
