import HolomorphicAnosov.Linear.HyperbolicDecayAux23

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov
noncomputable section
set_option maxRecDepth 2000
namespace RealDecayDescent
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
@[local simp] theorem realPart_tmul (z : ℂ) (v : V) : realPart (z ⊗ₜ[ℝ] v) = z.re • v := by
  simp [realPart]

end RealDecayDescent
end
end HolomorphicAnosov
