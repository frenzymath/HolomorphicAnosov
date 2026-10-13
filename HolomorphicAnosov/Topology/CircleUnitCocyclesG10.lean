import HolomorphicAnosov.Topology.CircleSingularCohomologyWindingBaseG10
import HolomorphicAnosov.Topology.SingularConstantOneCocycleG10

/-!
# Normalized degree-zero cocycles on the circle and point

Source: Hatcher, *Algebraic Topology*, pp. 197–198 and 207. Apply the generic
constant-one singular cocycle construction to the actual circle and point.
The evaluation is the literal cochain value on a coefficient-one simplex.
-/

open scoped Simplicial

namespace HolomorphicAnosov.CircleSingularCohomology

/-- The circle and point have degree-zero cocycles taking value one on every
coefficient-one singular zero-simplex.

Source: Hatcher, *Algebraic Topology*, pp. 197–198 and 207. Apply
`SingularCochain.exists_constantOne_cocycle` to each carrier. Its `simplexValue`
normalization is definitionally the target's `cocycleEval` on `simplexChain`.
The construction uses cancellation of the two endpoint values and is valid
in every field, including characteristic two. -/
theorem exists_circle_point_unit_cocycles (K : Type) [Field K] :
    ∃ (u : cocycles K circleSpace 0) (up : cocycles K pointSpace 0),
      (∀ σ : singularSet circleSpace _⦋0⦌,
        cocycleEval K circleSpace 0 u (simplexChain K circleSpace 0 σ) = 1) ∧
      (∀ σ : singularSet pointSpace _⦋0⦌,
        cocycleEval K pointSpace 0 up (simplexChain K pointSpace 0 σ) = 1) := by
  obtain ⟨u, _, hu⟩ := SingularCochain.exists_constantOne_cocycle K circleSpace
  obtain ⟨up, _, hup⟩ := SingularCochain.exists_constantOne_cocycle K pointSpace
  exact ⟨u, up, hu, hup⟩

end HolomorphicAnosov.CircleSingularCohomology
