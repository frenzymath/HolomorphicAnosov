import HolomorphicAnosov.Linear.HyperbolicDecayAux15

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov

/-- The continuous linear map underlying a power of an automorphism is the corresponding power of its map. -/
theorem equiv_pow_map
    {𝕜 W : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (T : W ≃L[𝕜] W) (n : ℕ) : (T ^ n).toContinuousLinearMap = T.toContinuousLinearMap ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ, ContinuousLinearEquiv.toContinuousLinearMap_mul, ih]



end HolomorphicAnosov
