import HolomorphicAnosov.Paper.Zhang.IntegralToralMap

namespace HolomorphicAnosov

/-- Composition of the actual row-coordinate toral maps is matrix multiplication.
Source: Manning's integral algebraic target; expand finite sums, exchange their
order, and use the literal integer-module multiplication law. -/
theorem integral_toral_map_comp
    {n : ℕ} (A B : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (x : UnitAddTorus (Fin n)) :
    integralToralMap A (integralToralMap B x) = integralToralMap (A * B) x := by
  classical
  funext i
  change (∑ j : Fin n, A i j • ∑ k : Fin n, B j k • x k) =
    ∑ k : Fin n, (∑ j : Fin n, A i j * B j k) • x k
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]

end HolomorphicAnosov
