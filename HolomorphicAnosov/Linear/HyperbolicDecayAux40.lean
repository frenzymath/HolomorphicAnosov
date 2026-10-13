import HolomorphicAnosov.Linear.HyperbolicDecayAux39

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov
noncomputable section
set_option maxRecDepth 2000
namespace RealDecayDescent
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Every eigenvalue of the complexified automorphism in coordinates is an eigenvalue of its tensor
scalar extension. -/
theorem complexified_hasEigenvalue (A : V ≃L[ℝ] V) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (complexified A).toLinearEquiv.toLinearMap μ) :
    Module.End.HasEigenvalue (A.toLinearEquiv.toLinearMap.baseChange ℂ) μ := by
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := tensorCoordinates.symm w)
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  refine ⟨?_, ?_⟩
  · have hEq := congrArg tensorCoordinates.symm hw.apply_eq_smul
    change tensorCoordinates.symm (tensorCoordinates
      ((A.toLinearEquiv.baseChange ℝ ℂ) (tensorCoordinates.symm w))) =
        tensorCoordinates.symm (μ • w) at hEq
    rw [LinearEquiv.symm_apply_apply, map_smul] at hEq
    simpa only [← LinearEquiv.coe_toLinearMap, LinearEquiv.coe_baseChange] using hEq
  · intro heq
    exact hw.2 (tensorCoordinates.symm.injective (heq.trans (map_zero _).symm))



end RealDecayDescent
end
end HolomorphicAnosov
