import HolomorphicAnosov.Analysis.Regularity.MontgomeryDirectionalDerivativeDenseJointContinuity

/-!
This file proves dense joint continuity for a spatial partial derivative (Montgomery, 1945).
-/ 

namespace HolomorphicAnosov.Analysis.Regularity

open Set Filter
open scoped Topology _root_.Topology

/-- For each fixed spatial point, the parameters at which its coordinate partial derivative is jointly continuous form a dense Gδ set in the parameter subspace, with its original Euclidean subspace topology. (Montgomery, 1945) -/
theorem montgomery_parameter_derivative_dense_joint_continuity
    {r n : ℕ} (W : Set (EuclideanSpace ℝ (Fin r))) (hW : IsOpen W)
    (a : EuclideanSpace ℝ (Fin n)) (R : ℝ) (j : Fin n)
    (F H : EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ContinuousOn F (W ×ˢ Metric.ball a R))
    (hderiv : ∀ v ∈ W, ∀ y ∈ Metric.ball a R,
      HasDerivAt (fun t : ℝ ↦ F (v, y + t • EuclideanSpace.single j (1 : ℝ)))
        (H (v, y)) 0)
    (hH : ∀ v ∈ W, ContinuousOn (fun y ↦ H (v, y)) (Metric.ball a R)) :
    ∀ y₀ ∈ Metric.ball a R,
      Dense {v : W | ContinuousWithinAt H (W ×ˢ Metric.ball a R)
        (v.val, y₀)} ∧
      IsGδ {v : W | ContinuousWithinAt H (W ×ˢ Metric.ball a R)
        (v.val, y₀)} := by
  exact montgomery_directional_derivative_dense_joint_continuity W hW a R
    (EuclideanSpace.single j (1 : ℝ)) F H hF hderiv hH

end HolomorphicAnosov.Analysis.Regularity

