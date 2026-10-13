import HolomorphicAnosov.Geometry.RealTangentTopForm
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Complex
import Mathlib.Tactic.FinCases

namespace HolomorphicAnosov

variable {d : ℕ}

/-- A complex-linear map multiplies the paired real coordinate volume by the squared modulus of its complex determinant. (Demailly, I §1.B.5, p. 10; VI §4, p. 296). -/
theorem complexCoordinateTopForm_paired_map (A : ComplexModel d →ₗ[ℂ] ComplexModel d) :
    complexCoordinateTopForm d (fun i : ComplexPairedIndex d ↦
      A (Pi.single i.1 (if i.2 = 0 then (1 : ℂ) else Complex.I))) = ‖A.det‖ ^ 2 := by
  let b : Module.Basis (ComplexPairedIndex d) ℝ (ComplexModel d) :=
    (Pi.basis (fun _ : Fin d ↦ Complex.basisOneI)).reindex
      (Equiv.sigmaEquivProd (Fin d) (Fin 2))
  have hb (i : ComplexPairedIndex d) :
      b i = Pi.single i.1 (if i.2 = 0 then 1 else Complex.I) := by
    rcases i with ⟨i, j⟩
    calc
      b (i, j) = (Pi.basis (fun _ : Fin d ↦ Complex.basisOneI)) ⟨i, j⟩ :=
        (Pi.basis (fun _ : Fin d ↦ Complex.basisOneI)).reindex_apply
          (Equiv.sigmaEquivProd (Fin d) (Fin 2)) (i, j)
      _ = Pi.single i (Complex.basisOneI j) :=
        Pi.basis_apply (fun _ : Fin d ↦ Complex.basisOneI) ⟨i, j⟩
      _ = Pi.single i (if j = 0 then 1 else Complex.I) := by
        congr 1
        fin_cases j <;> simp [Complex.coe_basisOneI]
  have h := congrArg (fun f : AlternatingMap ℝ (ComplexModel d) ℝ
      (ComplexPairedIndex d) ↦ f ((A.restrictScalars ℝ) ∘ b))
    ((complexCoordinateTopForm d).toAlternatingMap.eq_smul_basis_det b)
  simp only [AlternatingMap.smul_apply, smul_eq_mul, Module.Basis.det_comp,
    Module.Basis.det_self, mul_one] at h
  have paired_coordinate_volume_one :
      complexCoordinateTopForm d (fun i : ComplexPairedIndex d ↦
        Pi.single i.1 (if i.2 = 0 then (1 : ℂ) else Complex.I)) = 1 := by
    change Matrix.det (fun i j : ComplexPairedIndex d ↦
      complexPairedCoordinates d
        (Pi.single i.1 (if i.2 = 0 then (1 : ℂ) else Complex.I)) j) = 1
    have hmat : (fun i j : ComplexPairedIndex d ↦
        complexPairedCoordinates d
          (Pi.single i.1 (if i.2 = 0 then (1 : ℂ) else Complex.I)) j) =
        (1 : Matrix (ComplexPairedIndex d) (ComplexPairedIndex d) ℝ) := by
      ext i j
      rcases i with ⟨i, a⟩
      rcases j with ⟨j, b⟩
      fin_cases a <;> fin_cases b <;> by_cases hij : i = j <;>
        simp [complexPairedCoordinates, Matrix.one_apply, hij, eq_comm]
    rw [hmat, Matrix.det_one]
  have hn : complexCoordinateTopForm d b = 1 := by
    simpa only [show (b : ComplexPairedIndex d → ComplexModel d) =
      (fun i ↦ Pi.single i.1 (if i.2 = 0 then 1 else Complex.I)) from funext hb]
      using paired_coordinate_volume_one
  change complexCoordinateTopForm d (fun i ↦ A (b i)) =
    complexCoordinateTopForm d b * (A.restrictScalars ℝ).det at h
  rw [hn, one_mul, LinearMap.det_restrictScalars, Algebra.norm_complex_apply,
    Complex.normSq_eq_norm_sq] at h
  simpa only [hb] using h

end HolomorphicAnosov
