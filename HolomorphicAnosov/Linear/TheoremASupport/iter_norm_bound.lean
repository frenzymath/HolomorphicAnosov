import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Topology.MetricSpace.Lipschitz

namespace HolomorphicAnosov.TheoremAProof

/-- The norm of the `n`th iterate of a continuous linear automorphism applied to `x` is at most
`‖T.toContinuousLinearMap‖ ^ n * ‖x‖`. -/
lemma iter_norm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E ≃L[ℝ] E) (x : E) (n : ℕ) :
    ‖(T : E → E)^[n] x‖ ≤ ‖T.toContinuousLinearMap‖ ^ n * ‖x‖ := by
  simpa using (T.toContinuousLinearMap.lipschitzWith.iterate n).dist_le_mul x 0


end HolomorphicAnosov.TheoremAProof
