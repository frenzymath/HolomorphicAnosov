import HolomorphicAnosov.Linear.HyperbolicDecayAux33

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov
noncomputable section
set_option maxRecDepth 2000
namespace RealDecayDescent
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem realPart_complexified (A : V ≃L[ℝ] V) (w : CoordinateSpace (V := V)) :
    coordinateRealPart (complexified A w) = A (coordinateRealPart w) := by
  change realPart (tensorCoordinates.symm (tensorCoordinates
    ((A.toLinearEquiv.baseChange ℝ ℂ) (tensorCoordinates.symm w)))) =
      A (realPart (tensorCoordinates.symm w))
  rw [LinearEquiv.symm_apply_apply]
  exact realPart_baseChange A.toLinearEquiv.toLinearMap _

end RealDecayDescent
end
end HolomorphicAnosov
