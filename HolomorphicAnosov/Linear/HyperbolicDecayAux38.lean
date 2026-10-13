import HolomorphicAnosov.Linear.HyperbolicDecayAux37

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov
noncomputable section
set_option maxRecDepth 2000
namespace RealDecayDescent
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The orbit of an embedded real vector under the complexified automorphism tends to zero exactly
when its real orbit does. (Alves, p. 17) -/
theorem embedding_decay_iff (A : V ≃L[ℝ] V) (v : V) :
    Tendsto (fun n : ℕ ↦ (complexified A ^ n) (coordinateEmbedding v)) atTop (𝓝 0) ↔
      Tendsto (fun n : ℕ ↦ (A ^ n) v) atTop (𝓝 0) := by
  constructor
  · intro h
    have h' := coordinateRealPart.continuous.tendsto 0 |>.comp h
    simpa only [Function.comp_def, realPart_complexified_pow,
      coordinateRealPart_embedding, map_zero] using h'
  · intro h
    have h' := coordinateEmbedding.continuous.tendsto 0 |>.comp h
    simpa only [Function.comp_def, ← complexified_pow_embedding, map_zero] using h'



end RealDecayDescent
end
end HolomorphicAnosov
