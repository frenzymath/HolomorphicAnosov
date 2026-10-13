import HolomorphicAnosov.Targets.Theorem12Support.RealMatrixComplexification.coordinate_equiv_intertwines
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
Complexification identifies a real matrix action with its entrywise complex cast and transfers eigenvalues and hyperbolicity to scalar extensions.
-/

noncomputable section
open TensorProduct

namespace HolomorphicAnosov.Theorem12MatrixScratch

variable {n : ℕ}

/-- The tensor-coordinate equivalence sends `z ⊗ x` to the vector with coordinates `(x i : ℂ) * z`. -/
theorem coordinate_equiv_tmul (z : ℂ) (x : Fin n → ℝ) :
    TensorProduct.piScalarRight ℝ ℂ ℂ (Fin n) (z ⊗ₜ[ℝ] x) =
      fun i ↦ (x i : ℂ) * z := by
  simp [Complex.real_smul]

/-- Every eigenvalue of the complexification of a real matrix action is an eigenvalue of its
entrywise complex cast. -/
theorem hasEigenvalue_complex_matrix_of_baseChange
    (M : Matrix (Fin n) (Fin n) ℝ) (μ : ℂ)
    (hμ : Module.End.HasEigenvalue ((Matrix.mulVecLin M).baseChange ℂ) μ) :
    Module.End.HasEigenvalue (Matrix.mulVecLin (fun i j ↦ (M i j : ℂ))) μ := by
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  apply Module.End.hasEigenvalue_of_hasEigenvector
    (x := TensorProduct.piScalarRight ℝ ℂ ℂ (Fin n) w)
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  refine ⟨?_, ?_⟩
  · rw [← coordinate_equiv_intertwines, hw.apply_eq_smul]
    exact (TensorProduct.piScalarRight ℝ ℂ ℂ (Fin n)).map_smul μ w
  · intro heq
    apply hw.2
    exact (TensorProduct.piScalarRight ℝ ℂ ℂ (Fin n)).injective
      (heq.trans (map_zero _).symm)

/-- If a real continuous linear equivalence acts by a matrix whose complex cast has no eigenvalue of
modulus one, its complexification has no eigenvalue of modulus one. -/
theorem hyperbolic_baseChange_of_matrix
    (M : Matrix (Fin n) (Fin n) ℝ)
    (R : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (hR : R.toLinearMap = Matrix.mulVecLin M)
    (hhyper : ∀ μ : ℂ,
      Module.End.HasEigenvalue (Matrix.mulVecLin (fun i j ↦ (M i j : ℂ))) μ →
        ‖μ‖ ≠ 1) :
    ∀ μ : ℂ, Module.End.HasEigenvalue (R.toLinearMap.baseChange ℂ) μ → ‖μ‖ ≠ 1 := by
  intro μ hμ
  rw [hR] at hμ
  exact hhyper μ (hasEigenvalue_complex_matrix_of_baseChange M μ hμ)

/-- If an invertible integer matrix has no complex eigenvalue of modulus one, the complexification
of its associated real continuous linear equivalence has no eigenvalue of modulus one. -/
theorem hyperbolic_integer_gl_baseChange
    (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (hhyper : ∀ μ : ℂ,
      Module.End.HasEigenvalue (Matrix.mulVecLin (fun i j ↦ (A i j : ℂ))) μ →
        ‖μ‖ ≠ 1) :
    ∀ μ : ℂ,
      Module.End.HasEigenvalue
        (((Matrix.GeneralLinearGroup.toLin
          (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) A)).toLinearEquiv.toContinuousLinearEquiv).toLinearMap.baseChange ℂ) μ → ‖μ‖ ≠ 1 := by
  apply hyperbolic_baseChange_of_matrix (fun i j ↦ (A i j : ℝ)) _ rfl
  simpa using hhyper


end HolomorphicAnosov.Theorem12MatrixScratch
