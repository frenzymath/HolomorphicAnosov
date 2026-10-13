import Mathlib.LinearAlgebra.Basis.Defs
import HolomorphicAnosov.Geometry.HermitianMatrixChangeDeterminant
import Mathlib.Analysis.InnerProductSpace.GramMatrix


namespace HolomorphicAnosov

set_option backward.isDefEq.respectTransparency false in
/-- The first-linear Hermitian Gram determinant of any finite vector family is the Gram determinant of a basis times the squared modulus of its coordinate determinant. (Demailly, VI §4.) -/
theorem hermitian_core_gram_det_change {d : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℂ V] (k : InnerProductSpace.Core ℂ V)
    (b : Module.Basis (Fin d) ℂ V) (v : Fin d → V) :
    (Matrix.det fun i j ↦ k.inner (v j) (v i)) =
      (Matrix.det fun i j ↦ k.inner (b j) (b i)) *
        (‖(Matrix.of fun i j ↦ b.repr (v j) i).det‖ ^ 2 : ℝ) := by
  let : InnerProductSpace.Core ℂ V := k
  let : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : InnerProductSpace ℂ V := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ V)
  let H : Matrix (Fin d) (Fin d) ℂ := fun i j ↦ k.inner (b j) (b i)
  let C : Matrix (Fin d) (Fin d) ℂ := fun i j ↦ b.repr (v j) i
  have hm : (fun i j ↦ k.inner (v j) (v i)) =
      C.transpose * H * C.map (starRingEnd ℂ) := by
    ext i j
    change inner ℂ (v j) (v i) = _
    rw [← b.sum_repr (v j), ← b.sum_repr (v i)]
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
    simp_rw [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro c hc
    dsimp [H, C]
    ring
  rw [hm, hermitian_matrix_change_det]
  rfl

end HolomorphicAnosov
