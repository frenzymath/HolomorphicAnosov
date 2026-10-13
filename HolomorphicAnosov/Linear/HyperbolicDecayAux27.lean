import HolomorphicAnosov.Linear.HyperbolicDecayAux26

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov
noncomputable section
set_option maxRecDepth 2000
namespace RealDecayDescent
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
/-- The embedding into the complexification intertwines a real endomorphism with its scalar
extension. -/
theorem embedding_baseChange (A : Module.End ℝ V) (v : V) :
    A.baseChange ℂ (realEmbedding v) = realEmbedding (A v) := by
  simp [realEmbedding, LinearMap.baseChange_tmul]




end RealDecayDescent
end
end HolomorphicAnosov
