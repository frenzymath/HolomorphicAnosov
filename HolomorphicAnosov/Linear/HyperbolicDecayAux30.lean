import HolomorphicAnosov.Linear.HyperbolicDecayAux29

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov
noncomputable section
set_option maxRecDepth 2000
namespace RealDecayDescent
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The continuous real-linear real-part map from the complex coordinate space to `V`. -/
def coordinateRealPart : CoordinateSpace (V := V) →L[ℝ] V :=
  (realPart.comp (tensorCoordinates.symm.toLinearMap.restrictScalars ℝ)).toContinuousLinearMap

end RealDecayDescent
end
end HolomorphicAnosov
