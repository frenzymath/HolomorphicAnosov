import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1.Definitions
import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1.No_periodic_complex_vector
import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1.Matrix_pow_mulVec

import HolomorphicAnosov.Paper.Zhang.IntegralToralMap
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.LinearAlgebra.Eigenspace.Matrix

namespace HolomorphicAnosov.Dynamics
open MeasureTheory
noncomputable section

theorem transpose_frequency_orbit_injective {n : ℕ} [NeZero n]
    (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (hroot : ∀ μ : ℂ,
      Module.End.HasEigenvalue (Matrix.mulVecLin (fun i j : Fin n ↦ (A i j : ℂ))) μ →
        ¬ IsOfFinOrder μ)
    (k : Fin n → ℤ) (hk : k ≠ 0) :
    Function.Injective (fun r : ℕ ↦ (A.val.transpose.mulVec)^[r] k) := by
  have hinj : Function.Injective A.val.transpose.mulVec := by
    intro x y h
    have h' := congrArg (A⁻¹.val.transpose.mulVec) h
    simpa only [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, A.mul_inv,
      Matrix.transpose_one, Matrix.one_mulVec] using h'
  have hperiod (r : ℕ) (hr : 0 < r) : (A.val.transpose.mulVec)^[r] k ≠ k := by
    intro h
    let M : Matrix (Fin n) (Fin n) ℂ := A.val.map (Int.castRingHom ℂ)
    let v : Fin n → ℂ := fun i ↦ (k i : ℂ)
    have hv : v ≠ 0 := by
      intro hv
      apply hk
      ext i
      have hi : (k i : ℂ) = 0 := congrFun hv i
      exact_mod_cast hi
    apply no_periodic_complex_vector M hroot r hr v hv
    ext i
    have hcast := congrArg (fun x : Fin n → ℤ ↦ (x i : ℂ)) h
    rw [← matrix_pow_mulVec] at hcast
    have hMt : (A.val.transpose ^ r).map (Int.castRingHom ℂ) = M.transpose ^ r := by
      rw [Matrix.map_pow]
      rfl
    change (Int.castRingHom ℂ) ((A.val.transpose ^ r).mulVec k i) =
      (Int.castRingHom ℂ) (k i) at hcast
    rw [RingHom.map_mulVec, hMt] at hcast
    exact hcast
  intro i j hij
  wlog hle : i ≤ j generalizing i j
  · exact (this hij.symm (Nat.le_of_not_ge hle)).symm
  by_cases he : i = j
  · exact he
  have hlt : i < j := lt_of_le_of_ne hle he
  have hfix : (A.val.transpose.mulVec)^[j - i] k = k := by
    apply hinj.iterate i
    rw [← Function.iterate_add_apply, Nat.add_sub_of_le hle]
    exact hij.symm
  exact False.elim (hperiod (j - i) (Nat.sub_pos_of_lt hlt) hfix)

end
end HolomorphicAnosov.Dynamics
