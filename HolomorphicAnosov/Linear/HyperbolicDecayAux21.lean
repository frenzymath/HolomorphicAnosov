import HolomorphicAnosov.Linear.HyperbolicDecayAux20

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov
noncomputable section
set_option maxRecDepth 2000
namespace RealDecayDescent
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The complex-linear coordinate equivalence for `ℂ ⊗[ℝ] V` induced by a finite real basis of `V`. -/
def tensorCoordinates : (ℂ ⊗[ℝ] V) ≃ₗ[ℂ] (Fin (Module.finrank ℝ V) → ℂ) :=
  ((Module.finBasis ℝ V).baseChange ℂ).equivFun



end RealDecayDescent
end
end HolomorphicAnosov
