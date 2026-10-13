import HolomorphicAnosov.Linear.HyperbolicDecayAux24

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov
noncomputable section
set_option maxRecDepth 2000
namespace RealDecayDescent
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
@[local simp] theorem realPart_embedding (v : V) : realPart (realEmbedding v) = v := by
  simp [realEmbedding, realPart]



end RealDecayDescent
end
end HolomorphicAnosov
