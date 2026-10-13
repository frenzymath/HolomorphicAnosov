import HolomorphicAnosov.Topology.CirclePositiveSimplexFacesG10
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic

/-!
# The positive circle simplex has zero singular boundary

Source: Hatcher, *Algebraic Topology*, Example 2.2 p.106 and the singular boundary
formula on p.108; pinned Mathlib `SSet.ιChainComplex_d`.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace HolomorphicAnosov.CircleSingularCohomology
noncomputable section

/-- The coefficient-one chain on the positive characteristic edge is a cycle.
Source: Hatcher, Example 2.2 p.106, with the literal alternating boundary
from Mathlib's singular simplicial-set chain complex.

Proof: The native boundary of its coproduct summand is the alternating sum
of the two endpoint summands. The endpoint-face equality identifies those
summands, so they cancel over every field, including characteristic two.
Evaluate this equality of morphisms at coefficient one. The outgoing index
of the degree-one chain complex is zero, giving the claimed kernel equation. -/
theorem positiveSimplex_isCycle (K : Type) [Field K] :
    ((chain K circleSpace).sc 1).g.hom
      (simplexChain K circleSpace 1 positiveSimplex) = 0 := by
  have h : (singularSet circleSpace).ιChainComplex
      (R := ModuleCat.of K K) positiveSimplex ≫
      ((singularSet circleSpace).chainComplex (ModuleCat.of K K)).d 1 0 = 0 := by
    rw [SSet.ιChainComplex_d]
    simp [Fin.sum_univ_two, positiveSimplex_faces]
  have hv := congrArg (fun F : ModuleCat.of K K ⟶
    ((singularSet circleSpace).chainComplex (ModuleCat.of K K)).X 0 ↦ F 1) h
  have hnext : (ComplexShape.down ℕ).next 1 = 0 :=
    (ComplexShape.down ℕ).next_eq' (ComplexShape.down_mk 1 0 rfl)
  change ((chain K circleSpace).d 1 ((ComplexShape.down ℕ).next 1))
    (simplexChain K circleSpace 1 positiveSimplex) = 0
  rw [hnext]
  exact hv

end
end HolomorphicAnosov.CircleSingularCohomology

