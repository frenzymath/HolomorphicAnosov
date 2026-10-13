import HolomorphicAnosov.Linear.HyperbolicDecayAux25

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov
noncomputable section
set_option maxRecDepth 2000
namespace RealDecayDescent
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
/-- Taking real parts intertwines the scalar extension of a real endomorphism with the original
endomorphism. -/
theorem realPart_baseChange (A : Module.End ℝ V) (w : ℂ ⊗[ℝ] V) :
    realPart (A.baseChange ℂ w) = A (realPart w) := by
  induction w using TensorProduct.inductionOn with
  | tmul z v => simp [LinearMap.baseChange_tmul, realPart]
  | add w v hw hv => simp only [map_add, hw, hv]



end RealDecayDescent
end
end HolomorphicAnosov
