import HolomorphicAnosov.Linear.HyperbolicDecayAux18

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov

/-- Convergence of the operator powers to zero implies convergence of every automorphism orbit to
zero. -/
theorem equiv_pointwise_decay_of_operator_decay
    {𝕜 W : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (T : W ≃L[𝕜] W)
    (h : Tendsto (fun n : ℕ ↦ T.toContinuousLinearMap ^ n) atTop (𝓝 0)) (v : W) :
    Tendsto (fun n : ℕ ↦ (T ^ n) v) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ ↦ (T ^ n).toContinuousLinearMap v) atTop (𝓝 0)
  simpa only [Function.comp_def, ← equiv_pow_map, zero_apply] using
    ((continuous_eval_const v).tendsto (0 : W →L[𝕜] W)).comp h

end HolomorphicAnosov
