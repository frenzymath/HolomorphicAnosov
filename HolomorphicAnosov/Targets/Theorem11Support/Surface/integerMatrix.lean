import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import HolomorphicAnosov.Targets.Theorem11Support.Surface.latticeEquiv

/-!
The matrix of a lattice automorphism in an integral basis lies in the integer general linear group.
-/

noncomputable section

namespace HolomorphicAnosov.Theorem11SupportW10

universe u

/-- The invertible integer matrix representing a lattice automorphism in the chosen integral basis. -/
def integerMatrix (L : FullComplexLattice 2) (B : LatticeLinearEquiv L)
    (b : Module.Basis (Fin 4) ℤ L.lattice) :
    Matrix.GeneralLinearGroup (Fin 4) ℤ where
  val := LinearMap.toMatrix b b (latticeEquiv L B).toLinearMap
  inv := LinearMap.toMatrix b b (latticeEquiv L B).symm.toLinearMap
  val_inv := by
    rw [← LinearMap.toMatrix_comp b b b]
    simp
  inv_val := by
    rw [← LinearMap.toMatrix_comp b b b]
    simp

end HolomorphicAnosov.Theorem11SupportW10

