import HolomorphicAnosov.Linear.HyperbolicDecayAux12

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov

/-- An automorphism commutes with its inverse as algebraic endomorphisms. -/
theorem equiv_commutes_inverse
    {𝕜 W : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (T : W ≃L[𝕜] W) :
    Commute T.toLinearEquiv.toLinearMap T.symm.toLinearEquiv.toLinearMap := by
  show T.toLinearEquiv.toLinearMap * T.symm.toLinearEquiv.toLinearMap =
    T.symm.toLinearEquiv.toLinearMap * T.toLinearEquiv.toLinearMap
  ext v
  simp

end HolomorphicAnosov
