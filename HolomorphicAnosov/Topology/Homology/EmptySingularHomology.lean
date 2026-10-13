import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov

/-- Ordinary singular homology of an empty space vanishes in every degree. (Hatcher) -/
theorem singular_homology_isZero_of_isEmpty {R : Type u} [Ring R]
    (X : TopCat.{u}) [IsEmpty X] (M : ModuleCat.{u} R) (n : ℕ) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).obj X) := by
  have hz : IsZero (((TopCat.toSSet.obj X).chainComplex M).X n) := by
    rw [IsZero.iff_id_eq_zero]
    apply SSet.chainComplex_hom_ext
    intro s
    exact isEmptyElim ((TopCat.toSSetObjEquiv X _) s (Classical.arbitrary _))
  exact ShortComplex.isZero_homology_of_isZero_X₂ _ hz

end HolomorphicAnosov
