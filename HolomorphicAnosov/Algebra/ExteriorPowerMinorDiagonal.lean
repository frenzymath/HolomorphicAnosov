import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin

open scoped Matrix
noncomputable section
namespace HolomorphicAnosov

/-- The diagonal coefficient of an exterior-power endomorphism in the ordered
wedge basis is the corresponding principal minor of its degree-one matrix.

Source: agent-written matrix-coordinate expansion of Hatcher, Algebraic Topology,
Example 3.13 p.213 and Example 3.16 p.216. Mathlib's exterior basis coordinate
functional evaluates a wedge as a determinant. Apply the map to each wedge factor
and use this formula. Its row/column convention gives the transpose of the ordered
principal submatrix; transpose preserves the determinant. Reindex the increasing
enumeration of the subset to its subtype. The empty subset gives determinant one.
-/
theorem exterior_power_minor_diagonal
    {V : Type*} [AddCommGroup V] [Module ℚ V] (n k : ℕ)
    (b : Module.Basis (Fin n) ℚ V) (f : V →ₗ[ℚ] V)
    (S : Set.powersetCard (Fin n) k) :
    (b.exteriorPower k).repr
      (exteriorPower.map k f (b.exteriorPower k S)) S =
    ((LinearMap.toMatrix b b f).submatrix
      (Subtype.val : S.val → Fin n) (Subtype.val : S.val → Fin n)).det := by
  classical
  rw [exteriorPower.basis_repr_apply, exteriorPower.basis_apply,
    exteriorPower.map_apply_ιMulti_family, exteriorPower.ιMulti_family,
    exteriorPower.ιMultiDual_apply_ιMulti]
  rw [← Matrix.det_submatrix_equiv_self (S.val.orderIsoOfFin S.property).toEquiv]
  rw [← Matrix.det_transpose]
  congr 1
  ext i j
  simp only [Matrix.transpose_apply, Matrix.of_apply, Function.comp_apply,
    Module.Basis.coord_apply, LinearMap.toMatrix_apply, Matrix.submatrix_apply,
    Set.powersetCard.ofFinEmbEquiv_symm_apply]
  rfl

end HolomorphicAnosov
