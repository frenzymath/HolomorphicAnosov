import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity

/-! # Paths from positive determinant matrices to the identity

We use the elementary generator argument behind the connected components of
GL(n,R). Mathlib's special-linear induction reduces determinant-one matrices
to transvections and two-coordinate diagonals (c,c⁻¹). The latter are products
of six transvections, by the same identity as `SpecialLinearGroup.diag2_decompose`.
Scale one diagonal coordinate to reduce a positive determinant to one.
Source: Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean:708–783.
-/

noncomputable section
open Matrix
namespace HolomorphicAnosov.PositiveMatrixPath
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A continuous path from M to the identity with nonzero determinant throughout.
Source: the elementary matrix-component construction described above. -/
def Good (M : Matrix ι ι ℝ) : Prop :=
  ∃ D : unitInterval → Matrix ι ι ℝ, Continuous D ∧ (∀ t, (D t).det ≠ 0) ∧
    D 0 = M ∧ D 1 = 1

/-- Multiply paths pointwise. Their determinants remain nonzero by multiplicativity,
and both endpoint equations follow by multiplication. Source: Matrix.det_mul. -/
lemma mul {A B : Matrix ι ι ℝ} (hA : Good A) (hB : Good B) : Good (A*B) := by
  obtain ⟨DA,hDA,ha,ha0,ha1⟩ := hA
  obtain ⟨DB,hDB,hb,hb0,hb1⟩ := hB
  exact ⟨fun t ↦ DA t * DB t, hDA.mul hDB, fun t ↦ by simp [ha t,hb t],
    by simp [ha0,hb0], by simp [ha1,hb1]⟩

/-- Shrink the transvection coefficient linearly to zero; its determinant is always
one. Source: Matrix.det_transvection_of_ne, Transvection.lean:135–136. -/
lemma transvection (i j : ι) (hij : i ≠ j) (c : ℝ) : Good (Matrix.transvection i j c) := by
  refine ⟨fun t ↦ Matrix.transvection i j ((1-(t:ℝ))*c), ?_, ?_, ?_, ?_⟩
  · apply continuous_matrix
    intro a b
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply]
    split_ifs <;> fun_prop
  · intro t
    simp [Matrix.det_transvection_of_ne _ _ hij]
  · simp
  · simp

/-- A two-coordinate diagonal (c,c⁻¹) is the product of six transvections.
Expand each transvection as 1 plus a single-entry matrix. The single-entry
multiplication rules reduce the identity to c*c⁻¹=1 on the two coordinates;
all other coordinates remain those of the identity. Source: the identity
`SpecialLinearGroup.diag2_decompose`, generalized from Fin 2 to arbitrary
selected indices, SpecialLinearGroup.lean:777–783. -/
lemma diag2n_decompose (i j : ι) (hij : i ≠ j) (c : ℝ) (hc : c ≠ 0) :
    (SpecialLinearGroup.diag2n hij c hc : Matrix ι ι ℝ) =
      Matrix.transvection i j c * Matrix.transvection j i (-c⁻¹) *
      Matrix.transvection i j c * Matrix.transvection i j (-1) *
      Matrix.transvection j i 1 * Matrix.transvection i j (-1) := by
  simp only [SpecialLinearGroup.diag2n_coe, Matrix.transvection,
    mul_add, add_mul, one_mul, mul_one,
    Matrix.single_mul_single_of_ne _ _ _ _ hij,
    Matrix.single_mul_single_of_ne _ _ _ _ hij.symm, Matrix.single_mul_single_same,
    add_zero]
  ext a b
  by_cases hai : a = i <;> by_cases haj : a = j <;>
    by_cases hbi : b = i <;> by_cases hbj : b = j <;>
    simp_all [Matrix.add_apply, Matrix.single_apply, Matrix.diagonal_apply,
      Matrix.one_apply, eq_comm]

/-- Every determinant-one matrix admits an invertible path to the identity.
Mathlib's special-linear induction reduces to transvections, two-coordinate
diagonals, and multiplication. The first shrink directly; the second are six
transvections; multiplication combines their paths pointwise.
Source: SpecialLinearGroup.diagonal_transvection_induction', lines 708–726. -/
lemma specialLinear [Nontrivial ι] (M : SpecialLinearGroup ι ℝ) : Good (M : Matrix ι ι ℝ) := by
  apply SpecialLinearGroup.diagonal_transvection_induction'
    (fun A ↦ Good (A : Matrix ι ι ℝ)) M
  · intro i j hij c hc
    rw [diag2n_decompose i j hij c hc]
    exact mul (mul (mul (mul (mul (transvection i j hij c)
      (transvection j i hij.symm (-c⁻¹))) (transvection i j hij c))
      (transvection i j hij (-1))) (transvection j i hij.symm 1))
      (transvection i j hij (-1))
  · intro i j hij c
    exact transvection i j hij c
  · intro A B hA hB
    exact mul hA hB

/-- Interpolate each positive diagonal entry r_i linearly to 1. Its coefficient
(1-t)r_i+t stays positive, so their product determinant stays nonzero. Source:
the elementary positive diagonal interpolation in the real GL component proof. -/
lemma positiveDiagonal (r : ι → ℝ) (hr : ∀ i, 0 < r i) : Good (Matrix.diagonal r) := by
  refine ⟨fun t ↦ Matrix.diagonal (fun i ↦ (1-(t:ℝ))*r i+t), ?_, ?_, ?_, ?_⟩
  · apply continuous_matrix
    intro i j
    simp only [Matrix.diagonal_apply]
    split_ifs <;> fun_prop
  · intro t
    rw [Matrix.det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    apply ne_of_gt
    by_cases ht : (t:ℝ) = 1
    · simp [ht]
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (sub_pos.mpr (lt_of_le_of_ne t.2.2 ht)) (hr i)) t.2.1
  · simp
  · simp

/-- Every positive determinant matrix on a finite nontrivial index type has an
invertible path to the identity. Choose an index i, and let R be diagonal with
det M at i and 1 elsewhere. All entries of R are positive. Its inverse S has
entry (det M)⁻¹ at i; hence A=S*M has determinant one. Contract R by positive
diagonal interpolation and A by special-linear generator induction. Their
pointwise product is the required path from R*A=M to the identity.
Source: Mathlib's special-linear generator induction, with this elementary
positive-determinant normalization (agent deduction). -/
lemma positive [Nontrivial ι] (M : Matrix ι ι ℝ) (hM : 0 < M.det) : Good M := by
  classical
  obtain ⟨i⟩ := ‹Nontrivial ι›.to_nonempty
  let r : ι → ℝ := fun k ↦ if k=i then M.det else 1
  let s : ι → ℝ := fun k ↦ if k=i then M.det⁻¹ else 1
  have hr : ∀ k, 0 < r k := by intro k; dsimp [r]; split_ifs <;> positivity
  have hdetS : (Matrix.diagonal s).det = M.det⁻¹ := by
    simp [s, Matrix.det_diagonal]
  have hSR : Matrix.diagonal r * Matrix.diagonal s = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    have h : (fun k ↦ r k * s k) = fun _ ↦ (1:ℝ) := by
      funext k
      dsimp [r,s]
      split_ifs <;> simp [hM.ne']
    rw [h]
    exact Matrix.diagonal_one
  let A : SpecialLinearGroup ι ℝ := ⟨Matrix.diagonal s * M, by
    simp [Matrix.det_mul, hdetS, hM.ne']⟩
  have h := mul (positiveDiagonal r hr) (specialLinear A)
  have heq : Matrix.diagonal r * (A : Matrix ι ι ℝ) = M := by
    change Matrix.diagonal r * (Matrix.diagonal s * M) = M
    rw [← Matrix.mul_assoc, hSR, Matrix.one_mul]
  rwa [heq] at h

end HolomorphicAnosov.PositiveMatrixPath
