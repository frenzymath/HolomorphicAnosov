import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Module

/-! This file defines the toral automorphism induced by an invertible integer matrix. (Zhang, Theorem 1.1) -/

namespace HolomorphicAnosov

/-- The integral toral map of an invertible integer matrix. (Zhang, Theorem 1.1) -/
noncomputable def integralToralMap {n : ℕ}
    (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (x : UnitAddTorus (Fin n)) : UnitAddTorus (Fin n) :=
  fun i ↦ ∑ j : Fin n, A i j • x j

end HolomorphicAnosov
