import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

open CategoryTheory AlgebraicTopology
open scoped Simplicial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace HolomorphicAnosov.Topology

/-- A one-simplex with equal endpoint faces has zero boundary, for every coefficient.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 p.166; this is the degree-one
alternating face differential and does not require the simplicial set to be singular. -/
theorem simplicial_one_simplex_isCycle
    (X : SSet.{u}) (R : ModuleCat.{u} ℤ) (s : X _⦋1⦌) (hs : X.δ 0 s = X.δ 1 s) (r : R) :
    (X.ιChainComplex (R := R) s).hom r ∈
      LinearMap.ker ((X.chainComplex R).sc 1).g.hom := by
  change ((X.chainComplex R).sc 1).g.hom ((X.ιChainComplex (R := R) s).hom r) = 0
  dsimp +instances only [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
    HomologicalComplex.shortComplexFunctor']
  change ((X.chainComplex R).d 1 ((ComplexShape.down ℕ).next 1)).hom
    ((X.ιChainComplex (R := R) s).hom r) =
      (0 : (X.chainComplex R).X ((ComplexShape.down ℕ).next 1))
  rw [ComplexShape.next_eq' (ComplexShape.down ℕ) (show (ComplexShape.down ℕ).Rel 1 0 from rfl)]
  have h := X.ιChainComplex_d (R := R) s
  have hzero : X.ιChainComplex (R := R) s ≫ (X.chainComplex R).d 1 0 = 0 := by
    rw [h]
    simp [Fin.sum_univ_two, hs]
  exact congrArg (fun f ↦ f.hom r) hzero

end HolomorphicAnosov.Topology

