import HolomorphicAnosov.Paper.Zhang.HyperbolicRealToralConjugacy
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! An invertible integer matrix defines a continuous real linear automorphism on the coordinate
vector space. Its action and inverse agree with the corresponding integer-matrix formulas.
(Zhang, §3, p. 11) -/

namespace HolomorphicAnosov.Theorem12RealToralModel

/-- The continuous real linear automorphism induced by an invertible integer matrix. (Zhang, §3, p.
11) -/
noncomputable def realCLE {n : ℕ} (A : Matrix.GeneralLinearGroup (Fin n) ℤ) :
    (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
  (Matrix.GeneralLinearGroup.toLin
    (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) A)).toLinearEquiv.toContinuousLinearEquiv

/-- The real dimension of `Fin n → ℝ` is `n`. -/
theorem real_dimension (n : ℕ) : Module.finrank ℝ (Fin n → ℝ) = n := by
  simp

/-- The linear map underlying `realCLE A` is multiplication by the real matrix obtained from `A`. -/
theorem realCLE_toLinearMap {n : ℕ} (A : Matrix.GeneralLinearGroup (Fin n) ℤ) :
    (realCLE A).toLinearMap = Matrix.mulVecLin (fun i j ↦ (A i j : ℝ)) := rfl

/-- The `i`th coordinate of `realCLE A v` is the sum of `(A i j : ℝ) * v j` over `j`. -/
theorem realCLE_apply {n : ℕ} (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (v : Fin n → ℝ) (i : Fin n) :
    realCLE A v i = ∑ j, (A i j : ℝ) * v j := rfl

/-- The inverse of `realCLE A` is `realCLE A⁻¹`. -/
theorem realCLE_inv {n : ℕ} (A : Matrix.GeneralLinearGroup (Fin n) ℤ) :
    (realCLE A).symm = realCLE A⁻¹ := by
  rfl

end HolomorphicAnosov.Theorem12RealToralModel

