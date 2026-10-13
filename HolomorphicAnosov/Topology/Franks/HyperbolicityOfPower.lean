import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Complex.Basic

namespace HolomorphicAnosov

/-- Step 11(C6) in the Franks–Manning source proof. If an iterate of the
original integer winding matrix has no complex eigenvalue of modulus one,
neither does the original matrix. Entrywise complexification and the
matrix-to-endomorphism map preserve powers; an eigenvector of the original
matrix is an eigenvector of its power, with eigenvalue raised to that power.
This also covers exponent zero and the empty coordinate space.
Source: the elementary eigenvector-power step in the original-cover adaptation
of Manning (1974), Theorem A, pp.424–426 (Step 11(C6) of the parent). The
implementation composes the exact Mathlib primitives
`Matrix.map_pow`, `Matrix.toLin'_pow`, and `Module.End.HasEigenvalue.pow`. -/
theorem franks_manning_hyperbolic_of_matrix_power
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (m : ℕ)
    (hpower : ∀ μ : ℂ,
      Module.End.HasEigenvalue
        (Matrix.mulVecLin (fun i j ↦ ((A ^ m) i j : ℂ))) μ → ‖μ‖ ≠ 1) :
    ∀ μ : ℂ,
      Module.End.HasEigenvalue
        (Matrix.mulVecLin (fun i j ↦ (A i j : ℂ))) μ → ‖μ‖ ≠ 1 := by
  intro μ hμ hnorm
  have hmap : Matrix.mulVecLin (fun i j ↦ ((A ^ m) i j : ℂ)) =
      (Matrix.mulVecLin (fun i j ↦ (A i j : ℂ))) ^ m := by
    change Matrix.mulVecLin ((A ^ m).map (Int.castRingHom ℂ)) = _
    rw [Matrix.map_pow]
    exact Matrix.toLin'_pow _ m
  apply hpower (μ ^ m)
  · rw [hmap]
    exact hμ.pow m
  · simp only [norm_pow, hnorm, one_pow]

end HolomorphicAnosov

