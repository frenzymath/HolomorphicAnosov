import HolomorphicAnosov.Topology.CirclePositiveCycleG10

/-!
# Underlying chain of the positive circle cycle

Agent construction: the circle winding target requires its chosen cycle to have
underlying chain equal to the coefficient-one positive singular simplex.
`positiveCycle` packages precisely this chain in the native cycle kernel; the
following equality records the value projection of that explicit constructor.
-/

namespace HolomorphicAnosov.CircleSingularCohomology

/-- The packaged positive cycle has the prescribed underlying singular chain.
Agent construction, from the explicit kernel-subtype constructor `positiveCycle`.
Proof: unfold that constructor and project its first component. The equality is
reflexive over every field, independently of its characteristic. -/
theorem positiveCycle_val (K : Type) [Field K] :
    (positiveCycle K).val = simplexChain K circleSpace 1 positiveSimplex := rfl

end HolomorphicAnosov.CircleSingularCohomology

