import HolomorphicAnosov.Topology.Homology.SingularChainCompactSupport
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Limits.IsLimit

/-!
Source: Hatcher, *Algebraic Topology*, p.108, the free singular chain groups,
together with the pinned Mathlib coproduct uniqueness equations in
`Mathlib/CategoryTheory/Limits/IsLimit.lean`, lines 158--166.  The canonical
coefficient equivalence sends each native singular-simplex summand to the
corresponding finitely supported single coefficient.
-/

noncomputable section

namespace HolomorphicAnosov

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

/-- The canonical coefficient equivalence maps every native singular generator
to the corresponding `Finsupp.single` coefficient.

Source: Hatcher, *Algebraic Topology*, p.108, and the canonical coproduct
isomorphism equations in Mathlib `CategoryTheory/Limits/IsLimit.lean:158--166`.

Proof: The native chain module and the finitely supported coefficient module
are colimit points of the same constant diagram, by
`SSet.isColimitChainComplexXCofan` and `ModuleCat.finsuppCoconeIsColimit`.
The canonical colimit-point isomorphism defining
`integralSingularChainCoefficients` commutes with the inclusion of each summand.
Evaluate that equality of linear maps at `z`. The native inclusion followed
by the isomorphism is the left-hand side, while the Finsupp coproduct inclusion
evaluated at `z` is `Finsupp.single σ z`, proving the asserted equality. -/
theorem integralSingularChainCoefficients_ι (X : TopCat.{u}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌)) (z : ULift.{u} ℤ) :
    integralSingularChainCoefficients X n
      (((TopCat.toSSet.obj X).ιChainComplex
        (R := ModuleCat.of ℤ (ULift.{u} ℤ)) σ).hom z) =
      Finsupp.single σ z := by
  have h := ((TopCat.toSSet.obj X).isColimitChainComplexXCofan
    (ModuleCat.of ℤ (ULift.{u} ℤ)) n).comp_coconePointUniqueUpToIso_hom
    (ModuleCat.finsuppCoconeIsColimit ℤ (ULift.{u} ℤ)
      ((TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌))) (Discrete.mk σ)
  exact congrArg (fun k ↦ k.hom z) h

end HolomorphicAnosov
