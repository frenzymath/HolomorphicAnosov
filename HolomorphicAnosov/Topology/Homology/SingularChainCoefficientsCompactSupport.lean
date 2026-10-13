import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex

noncomputable section
namespace HolomorphicAnosov
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe u

abbrev SingularChain (X : TopCat.{u}) (R : ModuleCat.{u} ℤ) (n : ℕ) :=
  ((TopCat.toSSet.obj X).chainComplex R).X n

def singularChainCoefficients (X : TopCat.{u}) (R : ModuleCat.{u} ℤ) (n : ℕ)
    (c : SingularChain X R n) :
      ((ModuleCat.finsuppCocone ℤ (R : Type u)
        ((TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌))).pt : Type u) := by
  let e := ((TopCat.toSSet.obj X).isColimitChainComplexXCofan R n).coconePointUniqueUpToIso
    (ModuleCat.finsuppCoconeIsColimit ℤ (R : Type u)
      ((TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌)))
  exact e.hom.hom' c

def singularChainImageSupport (X : TopCat.{u}) (R : ModuleCat.{u} ℤ) (n : ℕ)
    (c : SingularChain X R n) : Set X :=
  ⋃ σ ∈ (singularChainCoefficients X R n c).support,
    Set.range (TopCat.toSSetObjEquiv X (Opposite.op ⦋n⦌) σ)

theorem singularChainImageSupport_isCompact (X : TopCat.{u}) (R : ModuleCat.{u} ℤ)
    (n : ℕ) (c : SingularChain X R n) :
    IsCompact (singularChainImageSupport X R n c) := by
  apply (singularChainCoefficients X R n c).support.isCompact_biUnion
  intro σ hσ
  exact isCompact_range (TopCat.toSSetObjEquiv X (Opposite.op ⦋n⦌) σ).continuous

end HolomorphicAnosov
