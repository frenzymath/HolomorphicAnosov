import HolomorphicAnosov.Linear.HyperbolicDecayAux35

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov
noncomputable section
set_option maxRecDepth 2000
namespace RealDecayDescent
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem complexified_pow_embedding (A : V ≃L[ℝ] V) (n : ℕ) (v : V) :
    (complexified A ^ n) (coordinateEmbedding v) = coordinateEmbedding ((A ^ n) v) := by
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [pow_succ', pow_succ']
    change complexified A ((complexified A ^ n) (coordinateEmbedding v)) =
      coordinateEmbedding (A ((A ^ n) v))
    rw [hn, complexified_embedding]

end RealDecayDescent
end
end HolomorphicAnosov
