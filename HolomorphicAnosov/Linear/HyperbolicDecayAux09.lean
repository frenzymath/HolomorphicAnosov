import HolomorphicAnosov.Linear.HyperbolicDecayAux08

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov

/-- For an automorphism, an eigenvalue of the inverse gives the reciprocal eigenvalue for the forward map. (Alves, Lemma 2.3) -/
theorem eigenvalue_inverse_reciprocal
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (T : W ≃L[ℂ] W) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue T.symm.toLinearEquiv.toLinearMap μ) :
    μ ≠ 0 ∧ Module.End.HasEigenvalue T.toLinearEquiv.toLinearMap μ⁻¹ := by
  obtain ⟨v, hv, hvne⟩ := hμ.exists_hasEigenvector
  have heq : T.symm v = μ • v := Module.End.mem_eigenspace_iff.mp hv
  have hne : μ ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at heq
    exact hvne (T.symm.injective (by simpa using heq))
  refine ⟨hne, Module.End.hasEigenvalue_of_hasEigenvector ⟨?_, hvne⟩⟩
  apply Module.End.mem_eigenspace_iff.mpr
  have heq' : v = μ • T v := by
    simpa only [T.apply_symm_apply, map_smul] using congrArg T heq
  calc
    T v = μ⁻¹ • (μ • T v) := by simp [hne]
    _ = μ⁻¹ • v := congrArg (fun z ↦ μ⁻¹ • z) heq'.symm



end HolomorphicAnosov
