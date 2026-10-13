import HolomorphicAnosov.Linear.HyperbolicDecayAux34

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov
noncomputable section
set_option maxRecDepth 2000
namespace RealDecayDescent
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

@[local simp] theorem complexified_symm (A : V ≃L[ℝ] V) :
    complexified A.symm = (complexified A).symm := by
  apply ContinuousLinearEquiv.ext
  funext w
  change tensorCoordinates ((A.symm.toLinearEquiv.baseChange ℝ ℂ)
    (tensorCoordinates.symm w)) = tensorCoordinates
      ((A.toLinearEquiv.baseChange ℝ ℂ).symm (tensorCoordinates.symm w))
  rw [ContinuousLinearEquiv.toLinearEquiv_symm, LinearEquiv.baseChange_symm]

end RealDecayDescent
end
end HolomorphicAnosov
