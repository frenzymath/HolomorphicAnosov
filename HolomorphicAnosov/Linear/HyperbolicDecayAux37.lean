import HolomorphicAnosov.Linear.HyperbolicDecayAux36

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov
noncomputable section
set_option maxRecDepth 2000
namespace RealDecayDescent
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem realPart_complexified_pow (A : V ≃L[ℝ] V) (n : ℕ)
    (w : CoordinateSpace (V := V)) :
    coordinateRealPart ((complexified A ^ n) w) = (A ^ n) (coordinateRealPart w) := by
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [pow_succ', pow_succ']
    change coordinateRealPart (complexified A ((complexified A ^ n) w)) =
      A ((A ^ n) (coordinateRealPart w))
    rw [realPart_complexified, hn]



end RealDecayDescent
end
end HolomorphicAnosov
