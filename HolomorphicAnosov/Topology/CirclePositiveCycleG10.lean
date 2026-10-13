import HolomorphicAnosov.Topology.CirclePositiveSimplexCycleG10

namespace HolomorphicAnosov.CircleSingularCohomology
noncomputable section

/-- The normalized positive circle edge packaged as the actual cycle-kernel
object used by the winding target. -/
def positiveCycle (K : Type) [Field K] : chainCycles K circleSpace 1 :=
  ⟨simplexChain K circleSpace 1 positiveSimplex, positiveSimplex_isCycle K⟩

end
end HolomorphicAnosov.CircleSingularCohomology

