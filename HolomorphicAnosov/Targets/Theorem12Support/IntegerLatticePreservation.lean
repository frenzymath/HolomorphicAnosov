import HolomorphicAnosov.Targets.Theorem12Support.IntegerLatticePreservation.matrix_preserves_integer_coordinates
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
Integer matrices preserve the integer-coordinate lattice, and invertible integer matrices map it onto itself. (Zhang, Theorem 1.2)
-/

namespace HolomorphicAnosov.IntegerLatticePreservation

variable {n : ℕ}

/-- An integer matrix maps a lattice characterized by integer coordinates into itself. -/
theorem matrix_maps_lattice (Γ : Submodule ℤ (Fin n → ℝ))
    (hΓ : ∀ v, v ∈ Γ ↔ ∀ i, ∃ z : ℤ, v i = (z : ℝ))
    (M : Matrix (Fin n) (Fin n) ℤ) :
    Set.MapsTo (Matrix.mulVecLin (fun i j ↦ (M i j : ℝ))) (Γ : Set _) Γ := by
  intro v hv
  exact (hΓ _).mpr (matrix_preserves_integer_coordinates M v ((hΓ _).mp hv))

/-- An invertible integer matrix and its inverse both preserve the integer-coordinate lattice `Γ`. -/
theorem integer_gl_maps_lattice_both (Γ : Submodule ℤ (Fin n → ℝ))
    (hΓ : ∀ v, v ∈ Γ ↔ ∀ i, ∃ z : ℤ, v i = (z : ℝ))
    (A : Matrix.GeneralLinearGroup (Fin n) ℤ) :
    Set.MapsTo (Matrix.mulVecLin (fun i j ↦ (A i j : ℝ))) (Γ : Set _) Γ ∧
    Set.MapsTo (Matrix.mulVecLin (fun i j ↦ (A⁻¹ i j : ℝ))) (Γ : Set _) Γ :=
  ⟨matrix_maps_lattice Γ hΓ A, matrix_maps_lattice Γ hΓ (↑(A⁻¹) : Matrix (Fin n) (Fin n) ℤ)⟩

/-- An invertible integer matrix maps the integer-coordinate lattice `Γ` onto itself. -/
theorem integer_gl_image_lattice (Γ : Submodule ℤ (Fin n → ℝ))
    (hΓ : ∀ v, v ∈ Γ ↔ ∀ i, ∃ z : ℤ, v i = (z : ℝ))
    (A : Matrix.GeneralLinearGroup (Fin n) ℤ) :
    Matrix.mulVecLin (fun i j ↦ (A i j : ℝ)) '' (Γ : Set _) = (Γ : Set _) := by
  classical
  obtain ⟨hA, hAi⟩ := integer_gl_maps_lattice_both Γ hΓ A
  apply Set.Subset.antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact hA hv
  · intro v hv
    refine ⟨Matrix.mulVecLin (fun i j ↦ (A⁻¹ i j : ℝ)) v, hAi hv, ?_⟩
    change Matrix.mulVec (A.val.map (Int.castRingHom ℝ))
      (Matrix.mulVec ((A⁻¹).val.map (Int.castRingHom ℝ)) v) = v
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul]
    simp

/-- The real continuous linear equivalence associated with an invertible integer matrix maps the
integer-coordinate lattice `Γ` onto itself. -/
theorem integer_gl_realCLE_image_lattice (Γ : Submodule ℤ (Fin n → ℝ))
    (hΓ : ∀ v, v ∈ Γ ↔ ∀ i, ∃ z : ℤ, v i = (z : ℝ))
    (A : Matrix.GeneralLinearGroup (Fin n) ℤ) :
    ((Matrix.GeneralLinearGroup.toLin
      (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) A)).toLinearEquiv.toContinuousLinearEquiv) '' (Γ : Set _) = (Γ : Set _) := by
  exact integer_gl_image_lattice Γ hΓ A

/-- The real continuous linear equivalence associated with an invertible integer matrix preserves
the integer span of the standard basis. -/
theorem integer_gl_realCLE_image_basis_span (A : Matrix.GeneralLinearGroup (Fin n) ℤ) :
    ((Matrix.GeneralLinearGroup.toLin
      (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) A)).toLinearEquiv.toContinuousLinearEquiv) ''
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n))) : Set (Fin n → ℝ)) =
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n))) : Set (Fin n → ℝ)) := by
  apply integer_gl_realCLE_image_lattice
  intro v
  simpa [eq_comm] using (Pi.basisFun ℝ (Fin n)).mem_span_iff_repr_mem ℤ v

end HolomorphicAnosov.IntegerLatticePreservation


