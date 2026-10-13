import HolomorphicAnosov.Linear.HyperbolicDecayAux32

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov
noncomputable section
set_option maxRecDepth 2000
namespace RealDecayDescent
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem complexified_embedding (A : V ≃L[ℝ] V) (v : V) :
    complexified A (coordinateEmbedding v) = coordinateEmbedding (A v) := by
  change tensorCoordinates ((A.toLinearEquiv.baseChange ℝ ℂ)
    (tensorCoordinates.symm (tensorCoordinates (realEmbedding v)))) =
      tensorCoordinates (realEmbedding (A v))
  rw [LinearEquiv.symm_apply_apply]
  simp [realEmbedding]

end RealDecayDescent
end
end HolomorphicAnosov
