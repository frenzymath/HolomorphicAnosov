import Mathlib.Analysis.Convex.StdSimplex

namespace HolomorphicAnosov.BarycentricGeometry

/-- The equal-weight barycenter of standard coordinate vertices is supported precisely
on its indexing set. Source: Schultz, Math 246A §I.2, Proposition 3, p.23;
expand the coordinate of the finite sum, which has only its matching index nonzero. -/
theorem standard_barycenter_coordinate {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (i : ι) :
    ((F.card : ℝ)⁻¹ • ∑ j ∈ F, (Pi.single j 1 : ι → ℝ)) i =
      if i ∈ F then (F.card : ℝ)⁻¹ else 0 := by
  classical
  simp [Pi.smul_apply, Finset.sum_apply, Pi.single_apply,
    mul_ite]

end HolomorphicAnosov.BarycentricGeometry
