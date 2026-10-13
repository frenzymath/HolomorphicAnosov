import HolomorphicAnosov.Linear.HyperbolicDecayAux30

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov
noncomputable section
set_option maxRecDepth 2000
namespace RealDecayDescent
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

@[local simp] theorem coordinateRealPart_embedding (v : V) :
    coordinateRealPart (coordinateEmbedding v) = v := by
  change realPart (tensorCoordinates.symm (tensorCoordinates (realEmbedding v))) = v
  rw [LinearEquiv.symm_apply_apply, realPart_embedding]



end RealDecayDescent
end
end HolomorphicAnosov
