import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition

/-!
# Degree-zero cohomology equals the cocycle module

Source: Hatcher, Algebraic Topology, p.198, and Mathlib
`ShortComplex.LeftHomologyData.isIso_π`.
DAG node: `topo.zero_cohomology_cycle_equiv_g10`.
-/

open CategoryTheory
universe u
namespace HolomorphicAnosov.SingularCochain
noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- In a nonnegative cochain complex there are no degree-zero boundaries,
so its literal zero-cocycle quotient projection is a linear equivalence.
Source: Hatcher, Algebraic Topology, p.198, the displayed unaugmented cochain
complex ends in C⁰ ← 0. Mathlib's explicit module homology data and the
isomorphism criterion for a zero incoming differential give the equivalence. -/
theorem exists_zero_cohomology_cycle_equiv (R : Type u) [CommRing R]
    (Q : CochainComplex (ModuleCat.{u} R) ℕ) :
    ∃ e : cycles R Q 0 ≃ₗ[R] quotient R Q 0,
      ∀ a, e a = (Q.sc 0).moduleCatLeftHomologyData.π a := by
  have hf : (Q.sc 0).f = 0 := by
    change Q.d ((ComplexShape.up ℕ).prev 0) 0 = 0
    rw [CochainComplex.prev_nat_zero]
    exact Q.shape 0 0 (by simp)
  have := (Q.sc 0).moduleCatLeftHomologyData.isIso_π hf
  exact ⟨(asIso (Q.sc 0).moduleCatLeftHomologyData.π).toLinearEquiv, fun _ ↦ rfl⟩

end
end HolomorphicAnosov.SingularCochain
