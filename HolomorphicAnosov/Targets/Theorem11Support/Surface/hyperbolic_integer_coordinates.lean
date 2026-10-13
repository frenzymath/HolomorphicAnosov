import HolomorphicAnosov.Paper.Zhang.TorusModel
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic

/-!
Hyperbolicity of a complex-linear map passes to its integer matrix in real coordinates. (Zhang, §2, p.4)
-/

noncomputable section

namespace HolomorphicAnosov.SurfaceSpectral

universe u

/-- If real coordinates intertwine a hyperbolic complex-linear map with an integer matrix, every
complex eigenvalue of that matrix has modulus different from one. -/
theorem hyperbolic_integer_coordinates {d n : ℕ}
    (B : ComplexModel d ≃ₗ[ℂ] ComplexModel d)
    (P : ComplexModel d ≃L[ℝ] (Fin n → ℝ))
    (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (hPB : ∀ v : ComplexModel d, ∀ i,
      P (B v) i = ∑ j, (A i j : ℝ) * P v j)
    (hB : ComplexLinearHyperbolic B.toLinearMap) :
    ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.mulVecLin (fun i j : Fin n ↦ (A i j : ℂ))) μ → ‖μ‖ ≠ 1 := by
  intro μ hμ
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  have he := hw.apply_eq_smul
  have hw0 : w ≠ 0 := hw.2
  let x : ComplexModel d := P.symm (fun i ↦ (w i).re)
  let y : ComplexModel d := P.symm (fun i ↦ (w i).im)
  have hPx : P x = fun i ↦ (w i).re := P.apply_symm_apply _
  have hPy : P y = fun i ↦ (w i).im := P.apply_symm_apply _
  have hx : B x = μ.re • x - μ.im • y := by
    apply P.injective
    ext i
    rw [hPB, map_sub, map_smul, map_smul]
    have hei := congrFun he i
    change (∑ j, (A i j : ℂ) * w j) = μ * w i at hei
    have hi := congrArg Complex.re hei
    simpa [hPx, hPy] using hi
  have hy : B y = μ.im • x + μ.re • y := by
    apply P.injective
    ext i
    rw [hPB, map_add, map_smul, map_smul]
    have hei := congrFun he i
    change (∑ j, (A i j : ℂ) * w j) = μ * w i at hei
    have hi := congrArg Complex.im hei
    simpa [hPx, hPy, add_comm] using hi
  have hu : B (x + Complex.I • y) = μ • (x + Complex.I • y) := by
    rw [map_add, map_smul, hx, hy]
    ext j : 1
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  have hv : B (x - Complex.I • y) = star μ • (x - Complex.I • y) := by
    rw [map_sub, map_smul, hx, hy]
    ext j : 1
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  by_cases hu0 : x + Complex.I • y = 0
  · have hv0 : x - Complex.I • y ≠ 0 := by
      intro hv0
      have hx0 : x = 0 := by
        have ht : (2 : ℂ) • x = 0 := by
          calc
            (2 : ℂ) • x = (x + Complex.I • y) + (x - Complex.I • y) := by module
            _ = 0 := by rw [hu0, hv0]; simp
        exact (smul_eq_zero.mp ht).resolve_left (by norm_num)
      have hy0 : y = 0 := by
        have ht : Complex.I • y = 0 := by simpa [hx0] using hu0
        exact (smul_eq_zero.mp ht).resolve_left Complex.I_ne_zero
      apply hw0
      ext i
      apply Complex.ext
      · have hi := congrFun hPx i
        simpa [hx0] using hi.symm
      · have hi := congrFun hPy i
        simpa [hy0] using hi.symm
    have hev : Module.End.HasEigenvalue B.toLinearMap (star μ) :=
      Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr hv, hv0⟩
    simpa using hB (star μ) hev
  · exact hB μ (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hu, hu0⟩)

end HolomorphicAnosov.SurfaceSpectral

