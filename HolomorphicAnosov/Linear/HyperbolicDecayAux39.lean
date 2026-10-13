import HolomorphicAnosov.Linear.HyperbolicDecayAux38

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov
noncomputable section
set_option maxRecDepth 2000
namespace RealDecayDescent
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The real part of a vector whose complexified orbit tends to zero has a real orbit tending to
zero. (Alves, p. 17) -/
theorem realPart_decay (A : V ≃L[ℝ] V) (w : CoordinateSpace (V := V))
    (h : Tendsto (fun n : ℕ ↦ (complexified A ^ n) w) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ (A ^ n) (coordinateRealPart w)) atTop (𝓝 0) := by
  have h' := coordinateRealPart.continuous.tendsto 0 |>.comp h
  simpa only [Function.comp_def, realPart_complexified_pow, map_zero] using h'



end RealDecayDescent
end
end HolomorphicAnosov
