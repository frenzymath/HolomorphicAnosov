import Mathlib.Algebra.Homology.ShortComplex.Homology

/-!
# Homology maps depend only on the middle component

Source: Mathlib's `ShortComplex.π_homologyMap_ι`. The formula expresses the
induced homology map between an epimorphism and a monomorphism using only
the middle component. DAG node: `algebra.short_complex_homology_map_middle`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov

/-- Source: Mathlib `ShortComplex.π_homologyMap_ι`.

Short-complex morphisms with the same middle component induce the same
homology map. Apply Mathlib's cycle-to-opcycle formula, then cancel the
epimorphic homology projection and monomorphic homology inclusion. -/
theorem shortComplex_homologyMap_eq_of_middle_eq
    {C : Type*} [Category* C] [HasZeroMorphisms C]
    {S T : ShortComplex C} [S.HasHomology] [T.HasHomology]
    (f g : S ⟶ T) (h : f.τ₂ = g.τ₂) :
    ShortComplex.homologyMap f = ShortComplex.homologyMap g := by
  apply (cancel_epi S.homologyπ).1
  apply (cancel_mono T.homologyι).1
  simp only [Category.assoc]
  rw [ShortComplex.π_homologyMap_ι f, ShortComplex.π_homologyMap_ι g, h]

end HolomorphicAnosov
