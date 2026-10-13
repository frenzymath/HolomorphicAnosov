import HolomorphicAnosov.Paper.Zhang.IntegralToralMap

namespace HolomorphicAnosov

/-- The finite integer row formula sends the original zero basepoint to zero. -/
theorem integralToralMap_zero {n : ℕ}
    (B : Matrix.GeneralLinearGroup (Fin n) ℤ) : integralToralMap B 0 = 0 := by
  ext i
  simp [integralToralMap]

end HolomorphicAnosov
