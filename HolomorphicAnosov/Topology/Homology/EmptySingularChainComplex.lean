import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits

open CategoryTheory CategoryTheory.Limits
namespace HolomorphicAnosov

universe u

/-- The ordinary singular chain complex of an empty topological space is zero in every degree and for every coefficient module. (Hatcher) -/
theorem singular_chain_isZero_of_isEmpty {R : Type*} [Ring R]
    (X : TopCat.{u}) [IsEmpty X] (M : ModuleCat.{u} R) :
    IsZero (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} R)).obj M).obj X) := by
  rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero]
  apply HomologicalComplex.hom_ext
  intro n
  apply SSet.chainComplex_hom_ext
  intro σ
  exact isEmptyElim
    ((TopCat.toSSetObjEquiv X _ σ) (Convexity.StdSimplex.single 0))

end HolomorphicAnosov

