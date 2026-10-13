import HolomorphicAnosov.Linear.HyperbolicDecayAux21

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov
noncomputable section
set_option maxRecDepth 2000
namespace RealDecayDescent
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The real-linear embedding of `V` into its complexification, sending `v` to `1 ⊗ₜ v`. -/
def realEmbedding : V →ₗ[ℝ] ℂ ⊗[ℝ] V := (TensorProduct.mk ℝ ℂ V) 1



end RealDecayDescent
end
end HolomorphicAnosov
