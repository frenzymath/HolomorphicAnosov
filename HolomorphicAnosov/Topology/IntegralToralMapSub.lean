import HolomorphicAnosov.Paper.Zhang.IntegralToralMap

namespace HolomorphicAnosov

/-- The original integral toral map preserves displacement. Source: Manning
Lemma 6 target canonical coordinates; native finite sums and integer scalar multiplication. -/
theorem integral_toral_map_sub
    {n : ℕ} (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (x y : UnitAddTorus (Fin n)) :
    integralToralMap A (x - y) = integralToralMap A x - integralToralMap A y := by
  funext i
  simp only [integralToralMap, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]

end HolomorphicAnosov
