import HolomorphicAnosov.Linear.HyperbolicDecayAux22

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov
noncomputable section
set_option maxRecDepth 2000
namespace RealDecayDescent
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The real-linear real-part map on the complexification, sending `z ⊗ₜ v` to `z.re • v`. -/
def realPart : (ℂ ⊗[ℝ] V) →ₗ[ℝ] V :=
  TensorProduct.lift (LinearMap.mk₂ ℝ (fun z : ℂ ↦ fun v : V ↦ z.re • v)
    (by intros; simp [add_smul])
    (by intros; simp [smul_smul])
    (by intros; simp [smul_add])
    (by intros; simp [smul_smul, mul_comm]))

end RealDecayDescent
end
end HolomorphicAnosov
