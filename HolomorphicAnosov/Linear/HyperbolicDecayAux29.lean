import HolomorphicAnosov.Linear.HyperbolicDecayAux28

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov
noncomputable section
set_option maxRecDepth 2000
namespace RealDecayDescent
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The continuous real-linear embedding of `V` into the complex coordinate space. -/
def coordinateEmbedding : V →L[ℝ] CoordinateSpace (V := V) :=
  ((tensorCoordinates.toLinearMap.restrictScalars ℝ).comp realEmbedding).toContinuousLinearMap



end RealDecayDescent
end
end HolomorphicAnosov
