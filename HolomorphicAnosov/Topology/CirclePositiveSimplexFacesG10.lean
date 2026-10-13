import HolomorphicAnosov.Topology.CircleSingularCohomologyWindingBaseG10

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace HolomorphicAnosov.CircleSingularCohomology
noncomputable section

/-- The two faces of the positive singular edge agree because the endpoint
values of `t ↦ exp (2πit)` are both the unit-circle point `1`.
Source: Hatcher, Example 2.2 p.105; endpoint identifications are the
pinned Mathlib `TopCat.δ_*_toSSetObj₁Equiv.symm` formulas. -/
theorem positiveSimplex_faces :
    (singularSet circleSpace).δ 0 positiveSimplex =
      (singularSet circleSpace).δ 1 positiveSimplex := by
  apply TopCat.toSSetObj₀Equiv.injective
  simp only [positiveSimplex, TopCat.δ_zero_toSSetObj₁Equiv.symm,
    TopCat.δ_one_toSSetObj₁Equiv.symm, Equiv.apply_symm_apply]
  change Circle.exp (2 * Real.pi * 1) = Circle.exp (2 * Real.pi * 0)
  apply Subtype.ext
  simp [Circle.coe_exp, Complex.exp_two_pi_mul_I]

end
end HolomorphicAnosov.CircleSingularCohomology

