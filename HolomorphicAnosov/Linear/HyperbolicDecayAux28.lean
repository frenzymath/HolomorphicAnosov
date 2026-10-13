import HolomorphicAnosov.Linear.HyperbolicDecayAux27

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov
noncomputable section
set_option maxRecDepth 2000
namespace RealDecayDescent
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The finite-dimensional complex coordinate space for the complexification of `V`. -/
abbrev CoordinateSpace := Fin (Module.finrank ℝ V) → ℂ



end RealDecayDescent
end
end HolomorphicAnosov
