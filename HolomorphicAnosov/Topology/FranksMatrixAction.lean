import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! Public real matrix action and complexification laws used by Franks's semiconjugacy.
Source: Franks, *Anosov Diffeomorphisms* (1970), pp. 70–71. -/

namespace HolomorphicAnosov.FranksMatrix

noncomputable section
open scoped TensorProduct

def realAction {n : ℕ} (A : Matrix.GeneralLinearGroup (Fin n) ℤ) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
  (Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) A)).toLinearEquiv

theorem realAction_apply {n : ℕ} (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (v : Fin n → ℝ) (i : Fin n) :
    realAction A v i = ∑ j, (A i j : ℝ) * v j := by
  rfl

theorem realAction_intCast {n : ℕ} (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (v : Fin n → ℤ) :
    realAction A (fun i ↦ (v i : ℝ)) =
      fun i ↦ ((Matrix.mulVec (A : Matrix (Fin n) (Fin n) ℤ) v i : ℤ) : ℝ) := by
  ext i
  rw [realAction_apply]
  simp [Matrix.mulVec, dotProduct]

theorem complexification_intertwining {n : ℕ}
    (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (v : ℂ ⊗[ℝ] (Fin n → ℝ)) :
    TensorProduct.piScalarRight ℝ ℂ ℂ (Fin n) ((realAction A).toLinearMap.baseChange ℂ v) =
      Matrix.mulVecLin (fun i j : Fin n ↦ (A i j : ℂ))
        (TensorProduct.piScalarRight ℝ ℂ ℂ (Fin n) v) := by
  induction v using TensorProduct.inductionOn with
  | tmul c v =>
      ext i
      simp only [LinearMap.baseChange_tmul, TensorProduct.piScalarRight_apply,
        TensorProduct.piScalarRightHom_tmul, Complex.real_smul]
      change (realAction A v i : ℂ) * c = _
      rw [realAction_apply]
      simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast]
      change (∑ j, (A i j : ℂ) * (v j : ℂ)) * c =
        ∑ j, (A i j : ℂ) * ((v j : ℂ) * c)
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy

theorem complexification_hyperbolic {n : ℕ}
    (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (hA : ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.mulVecLin (fun i j : Fin n ↦ (A i j : ℂ))) μ → ‖μ‖ ≠ 1) :
    ∀ μ : ℂ, Module.End.HasEigenvalue ((realAction A).toLinearMap.baseChange ℂ) μ →
      ‖μ‖ ≠ 1 := by
  intro μ hμ
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  apply hA μ
  apply Module.End.hasEigenvalue_of_hasEigenvector
    (x := TensorProduct.piScalarRight ℝ ℂ ℂ (Fin n) v)
  apply Module.End.hasEigenvector_iff.mpr
  refine ⟨?_, ?_⟩
  · apply Module.End.mem_eigenspace_iff.mpr
    rw [← complexification_intertwining A v, hv.apply_eq_smul, map_smul]
  · exact fun hz ↦ hv.2 ((TensorProduct.piScalarRight ℝ ℂ ℂ (Fin n)).injective
      (by simpa using hz))


end
end HolomorphicAnosov.FranksMatrix

