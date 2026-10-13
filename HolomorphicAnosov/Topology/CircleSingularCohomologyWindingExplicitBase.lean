import HolomorphicAnosov.Topology.CircleSingularCohomologyWindingBaseG10
import HolomorphicAnosov.Topology.CirclePositiveCycleValG10
import HolomorphicAnosov.Topology.CircleUnitCocyclesG10

open scoped Simplicial

namespace HolomorphicAnosov.CircleSingularCohomology
noncomputable section

/-- The explicit positive singular cycle and normalized degree-zero cocycles used by the
circle cohomology profile.  This packages the canonical cycle constructor and the
constant-one cocycle provider into the exact witnesses consumed by the profile theorem.
Source: Hatcher, Algebraic Topology, Example 2.2 p.105 and pp.197--198. -/
theorem circle_winding_explicit_base (K : Type) [Field K] :
    ∃ (z : chainCycles K circleSpace 1) (u : cocycles K circleSpace 0)
      (up : cocycles K pointSpace 0),
      z.val = simplexChain K circleSpace 1 positiveSimplex ∧
      (∀ σ : singularSet circleSpace _⦋0⦌,
        cocycleEval K circleSpace 0 u (simplexChain K circleSpace 0 σ) = 1) ∧
      (∀ σ : singularSet pointSpace _⦋0⦌,
        cocycleEval K pointSpace 0 up (simplexChain K pointSpace 0 σ) = 1) := by
  obtain ⟨u, up, hu, hup⟩ := exists_circle_point_unit_cocycles K
  exact ⟨positiveCycle K, u, up, positiveCycle_val K, hu, hup⟩

end
end HolomorphicAnosov.CircleSingularCohomology

