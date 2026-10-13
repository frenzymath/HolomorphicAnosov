import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Complex.Basic

open scoped Topology
open Filter Set _root_.Topology

universe u v
namespace HolomorphicAnosov

/-- C9's source theorem applies after a real change of basis. -/
theorem covering_conjugacy_spectral_coordinates_g15
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A : V ≃L[ℝ] V)
    (hA : ∀ μ : ℂ,
      Module.End.HasEigenvalue (A.toLinearEquiv.toLinearMap.baseChange ℂ) μ → ‖μ‖ ≠ 1) :
    ∃ e : V ≃L[ℝ] (Fin (Module.finrank ℝ V) → ℝ),
      ∀ μ : ℂ, Module.End.HasEigenvalue
        (((e.symm.toLinearEquiv.trans A.toLinearEquiv).trans e.toLinearEquiv).toLinearMap.baseChange ℂ)
          μ → ‖μ‖ ≠ 1 := by
  let e : V ≃L[ℝ] (Fin (Module.finrank ℝ V) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  refine ⟨e, ?_⟩
  intro μ hμ
  apply hA μ
  let ec := e.toLinearEquiv.baseChange ℝ ℂ
  let B := (e.symm.toLinearEquiv.trans A.toLinearEquiv).trans e.toLinearEquiv
  have hconj : B.toLinearMap.baseChange ℂ =
      ec.toLinearMap ∘ₗ A.toLinearEquiv.toLinearMap.baseChange ℂ ∘ₗ ec.symm.toLinearMap := by
    change (e.toLinearEquiv.toLinearMap ∘ₗ
      A.toLinearEquiv.toLinearMap ∘ₗ e.symm.toLinearEquiv.toLinearMap).baseChange ℂ = _
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp]
    rfl
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := ec.symm v)
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
  · apply ec.injective
    have heigen := hv.apply_eq_smul
    change (B.toLinearMap.baseChange ℂ) v = μ • v at heigen
    rw [hconj] at heigen
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, map_smul] using heigen
  · intro hz
    apply hv.2
    exact ec.symm.injective (hz.trans (map_zero ec.symm).symm)


end HolomorphicAnosov
